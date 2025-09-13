
import json
import numpy as np
from typing import List, Dict, Any, Optional
from langchain_community.vectorstores import Chroma
from langchain_huggingface import HuggingFaceEmbeddings
from langchain.schema import Document
import os

os.environ["HF_ENDPOINT"] = "https://hf-mirror.com"

# Auto-select device to avoid hanging when CUDA environment is incomplete
try:
	import torch  # Keep consistent with file's original indentation style (tabs)
	CUDA_AVAILABLE = torch.cuda.is_available()
except Exception:
	CUDA_AVAILABLE = False

def load_json_data(file_path: str) -> List[Dict[str, Any]]:
	"""Load JSON format data"""
	with open(file_path, 'r', encoding='utf-8') as f:
		data = json.load(f)
	return data


def validate_data_format(data: List[Dict[str, Any]]) -> bool:
	"""Validate data format"""
	required_fields = ['name','category','type', 'input', 'output', 'value', 'explanation']
	for item in data:
		if not all(field in item for field in required_fields):
			return False
	return True


class LangChainVectorDB:
	def __init__(self, persist_directory: str = "./VectorDB/chroma_db"):
		"""Initialize LangChain vector database"""
		self.persist_directory = persist_directory
		# Use a more stable model name and automatically use CPU when no GPU is available to avoid hanging during initialization
		model_name = "sentence-transformers/all-MiniLM-L6-v2"
		device = 'cuda' if CUDA_AVAILABLE else 'cpu'
		self.embeddings = HuggingFaceEmbeddings(
			model_name=model_name,
			model_kwargs={'device': device}
		)
		print(f"Embeddings initialized with model={model_name}, device={device}")
		self.vectorstore = None
		
		
	def create_documents(self, data: List[Dict[str, Any]]) -> List[Document]:
		"""Convert data to LangChain Document format"""
		documents = []
		for item in data:
			# Combine code and explanation
			content = item['value']
			
			# Create Document object
			doc = Document(
				page_content=content,
				metadata={
					"name": item['name'],
					"category": item['category'], # loop summary recursion predicate
					"type": item['type'], # numeric array linked_list
					"input": item['input'],
					"output": item['output'],
					"value": item['value'],
					"explanation": item['explanation']
				}
			)
			documents.append(doc)
		return documents
	
	def add_data(self, data: List[Dict[str, Any]]):
		"""Adding data to vector database"""
		documents = self.create_documents(data)
		
		self.vectorstore = Chroma.from_documents(
			documents=documents,
			embedding=self.embeddings,
			persist_directory=self.persist_directory
		)
		
	
	def load_existing_db(self):
		"""Load existing vector database"""
		if os.path.exists(self.persist_directory):
			self.vectorstore = Chroma(
				persist_directory=self.persist_directory,
				embedding_function=self.embeddings
			)
			return True
		return False
	
	def search_by_type(self, target_type: str, n_results: int = 5):
		"""Filter by Type"""
		if not self.vectorstore:
			raise ValueError("Vector database not initialized")
		
		# Use metadata filtering
		results = self.vectorstore.similarity_search(
			"",  # Empty query, only filter by metadata
			k=n_results,
			filter={"type": target_type}
		)
		return results
	
	def search_similar(self, query: str, target_type: str = None, target_category: str = None, n_results: int = 3):
		"""Similarity search"""
		if not self.vectorstore:
			raise ValueError("Vector database not initialized")
		# Assemble filter conditions
		filter_list = []
		if target_type is not None:
			filter_list.append({"type": {"$eq": target_type}})
		if target_category is not None:
			filter_list.append({"category": {"$eq": target_category}})
		if not filter_list:
			filter_dict = None
		elif len(filter_list) == 1:
			filter_dict = filter_list[0]
		else:
			filter_dict = {"$and": filter_list}
		
		results = self.vectorstore.similarity_search(
			query,
			k=n_results,
			filter=filter_dict
		)
		return results

	def search_by_metadata(self, target_type: Optional[str] = None, target_category: Optional[str] = None, n_results: int = 3):
		"""Filter only by metadata, without providing query vector."""
		if not self.vectorstore:
			raise ValueError("Vector database not initialized")
		filter_list = []
		if target_type is not None:
			filter_list.append({"type": {"$eq": target_type}})
		if target_category is not None:
			filter_list.append({"category": {"$eq": target_category}})
		if not filter_list:
			filter_dict = None
		elif len(filter_list) == 1:
			filter_dict = filter_list[0]
		else:
			filter_dict = {"$and": filter_list}
		return self.vectorstore.similarity_search("", k=n_results, filter=filter_dict)
	
	def get_all_documents(self):
		"""Get all documents"""
		if not self.vectorstore:
			raise ValueError("Vector database not initialized")
		return self.vectorstore.get()




def process_json_to_langchain_db(json_file: str, persist_directory: str = "./VectorDB/chroma_db", mode: str = "add"):
	"""
	Convert JSON data to LangChain vector database.
	Args:
		json_file (str): Path containing JSON data to process.
		persist_directory (str): Path to ChromaDB persistence directory.
		mode (str): Operation mode.
			- "init": Force create new database, delete old one if exists, then add all data from json_file.
			- "add": Add data from json_file to existing database. Create new database if it doesn't exist.
	Returns:
		LangChainVectorDB: Initialized or loaded vector database instance.
	Raises:
		ValueError: If data format is incorrect or mode is invalid.
	"""
	print("Initializing LangChain vector database object...")
	vector_db = LangChainVectorDB(persist_directory)
	if mode == "init":
		
		print(f"Mode: {mode} - Force create/update database and add data.")
		# Careful operation: Delete old database to ensure it's completely new
		if os.path.exists(persist_directory):
			print(f"Detected existing database at '{persist_directory}', deleting to reinitialize...")
			import shutil
			shutil.rmtree(persist_directory)
			print("Old database has been deleted.")

		# Load and add all data
		print("Loading JSON data...")
		data = load_json_data(json_file)
		if not validate_data_format(data):
			raise ValueError("Data format is incorrect, must contain name, category, type, input, output, value, explanation fields")
		
		print("Adding data to vector database...")
		vector_db.add_data(data)
		print(f"Successfully processed {len(data)} records and created database.")

	elif mode == "add":
		print(f"Mode: {mode} - Add data to existing (or new) database.")
		
		# Try to load existing database
		db_exists = vector_db.load_existing_db()
		
		# Load new data to add
		print("Loading JSON data to add...")
		data_to_add = load_json_data(json_file)
		if not validate_data_format(data_to_add):
			raise ValueError("Data to add format is incorrect, must contain name, category, type, input, output, value, explanation fields")

		if db_exists:
			print(f"Database already exists at '{persist_directory}'. Adding {len(data_to_add)} new records.")
			vector_db.add_data(data_to_add) 

		else:
			print("Database not found, creating and adding data.")
			vector_db.add_data(data_to_add)

		print(f"Successfully processed {len(data_to_add)} records and updated database.")

	return vector_db


def search_and_display(vector_db: LangChainVectorDB, query: str = None, target_type: str = None ,target_category: str = None):
	"""Search and display results
	
	If query and target_type are provided, first filter by type then search by query.
	If only target_type is provided, only filter by type.
	If only query is provided, perform global similarity search.
	"""
	
	if query:
		# When query exists, always perform similarity search and apply type filtering (if target_type is provided)
		results = vector_db.search_similar(query, target_type,target_category, n_results=5)
		if target_type:
			print(f"Filter by category '{target_category}' and type '{target_type}' then similarity search (query: '{query}'):")
		else:
			print(f"Global similarity search (query: '{query}'):")
	elif target_type:
		results = vector_db.search_by_type(target_type, n_results=5)
		print(f"Results filtered by type (Type: '{target_type}'):")
	else:
		print("Query or type not provided. Please provide 'query' or 'target_type','target_category' to search.")
		return

	for i, doc in enumerate(results):
		print(f"\nResult {i+1}:")
		print(f"Name: {doc.metadata['name']}")
		print(f"Category: {doc.metadata['category']}")
		print(f"Type: {doc.metadata['type']}")
		print(f"Input: {doc.metadata['input'][:100]}...")
		print(f"Output: {doc.metadata['output'][:100]}...")
		print(f"Explanation: {doc.metadata['explanation'][:100]}...")


def search_and_return(vector_db: LangChainVectorDB, query: str = None, target_type: str = None, target_category: str = None) -> list[str]:
	"""
	Searches and returns a list of structured English strings, with each string representing a single search result.

	If a query and target_type are provided, it first filters by type and category, then performs a similarity search.
	If only a target_type or target_category is provided, it filters by the specified metadata.
	If only a query is provided, it performs a similarity search across the entire database.
	"""
	results_list = []

	if query:
		results = vector_db.search_similar(query, target_type=target_type, target_category=target_category, n_results=1)
	elif target_type or target_category:
		results = vector_db.search_by_metadata(target_type=target_type, target_category=target_category, n_results=1)
	else:
		return ["Error: No query or filter criteria provided. Please supply either a 'query', 'target_type', or 'target_category' to perform a search."]

	if not results:
		return ["No relevant results found."]
	else:
		for i, doc in enumerate(results):
			doc_metadata = doc.metadata
			result_block = (
				f"Name: {doc_metadata.get('name', 'N/A')}\n"
				f"Category: {doc_metadata.get('category', 'N/A')}\n"
				f"Type: {doc_metadata.get('type', 'N/A')}\n"
				f"Input: {doc_metadata.get('input', 'N/A')}\n"
				f"Output: {doc_metadata.get('output', 'N/A')}\n"
				f"Value: {doc_metadata.get('value', 'N/A')}\n"
				f"Explanation: {doc_metadata.get('explanation', 'N/A')}\n"
			)
			results_list.append(result_block)

	return results_list



def get_statistics(vector_db: LangChainVectorDB):
	"""Get database statistics information"""
	print("========== Getting Database Statistics Information ===========")
	if not vector_db.vectorstore:
		print("Vector database not initialized")
		return
	
	# Get all documents
	all_docs = vector_db.get_all_documents()
	
	# Statistics type distribution
	type_counts = {}
	for metadata in all_docs['metadatas']:
		item_type = metadata['type']
		type_counts[item_type] = type_counts.get(item_type, 0) + 1
	
	print("Database statistics information:")
	print(f"Total records: {len(all_docs['ids'])}")
	print("Type distribution:")
	for item_type, count in type_counts.items():
		print(f"  {item_type}: {count} records")
	print("====================================")



def main():
	"""Main function"""
	
	
	print("=== Starting data processing ===")
	vector_db = process_json_to_langchain_db('VectorDB/Jsons/init.json',mode='init')
	get_statistics(vector_db)

	# search_and_display(vector_db, query="sort")
	results = search_and_return(vector_db, query="sort")
	for result in results:
		print(result)

if __name__ == "__main__":
	main()


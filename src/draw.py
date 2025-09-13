import matplotlib.pyplot as plt
import numpy as np
import matplotlib.lines as mlines

# --- 数据准备 ---
# 根据图片中的表格提取数据
labels = ['Unmasked', 'Masked']

# syGus 数据
sygus_asgse = [93.98, 80.45]
sygus_autospec = [85.71, 57.89]

# Frama-c 数据
frama_c_asgse = [70.83, 64.71]
frama_c_autospec = [60.78, 29.41]

# --- 绘图 ---
# 创建一个正方形图形
fig, ax = plt.subplots(figsize=(8, 8))

# 绘制 Frama-c 的线
ax.plot(labels, frama_c_asgse, color='red', linestyle='solid', marker='o', linewidth=2.5)
ax.plot(labels, frama_c_autospec, color='red', linestyle='dashed', marker='o', linewidth=2.5)

# 绘制 syGus 的线
ax.plot(labels, sygus_asgse, color='blue', linestyle='solid', marker='o', linewidth=2.5)
ax.plot(labels, sygus_autospec, color='blue', linestyle='dashed', marker='o', linewidth=2.5)

# --- 添加特定节点的灰色背景色 ---
# Found 'Masked' 节点的索引
node_index = labels.index('Masked')

# 为 syGus 的 'Masked' AutoSpec 节点添加背景
sygus_node_value = sygus_autospec[node_index]
ax.scatter(labels[node_index], sygus_node_value,
           s=350, color='lightgray', alpha=0.9, marker='o', zorder=0)
# 重新绘制该节点，确保它在背景之上
ax.plot(labels[node_index], sygus_node_value,
        color='blue', linestyle='dashed', marker='o', markersize=7, zorder=10, linewidth=2.5)

# 为 Frama-c 的 'Masked' AutoSpec 节点添加背景
frama_c_node_value = frama_c_autospec[node_index]
ax.scatter(labels[node_index], frama_c_node_value,
           s=350, color='lightgray', alpha=0.9, marker='o', zorder=0)
# 重新绘制该节点，确保它在背景之上
ax.plot(labels[node_index], frama_c_node_value,
        color='red', linestyle='dashed', marker='o', markersize=7, zorder=10, linewidth=2.5)


# --- 在节点上添加具体数字 ---
# 定义文本的垂直偏移量，防止与标记重叠
y_offset = 2

# 将所有数据和其Name放入一个列表，方便遍历
all_data = {
    "sygus_asgse": sygus_asgse,
    "sygus_autospec": sygus_autospec,
    "frama_c_asgse": frama_c_asgse,
    "frama_c_autospec": frama_c_autospec
}

# 遍历所有数据点并添加文本标签
for name, data_points in all_data.items():
    for i, value in enumerate(data_points):
        # 检查值是否有效 (不是 np.nan)
        if not np.isnan(value):
            ax.text(
                x=i,
                y=value + y_offset,
                s=f'{value:.2f}',
                ha='center',
                va='bottom',
                fontsize=12
            )

# --- 图表美化 ---
# 设置坐标轴范围
ax.set_ylim(0, 105)

# 设置坐标轴刻度和标签的字体大小
ax.tick_params(axis='x', labelsize=16)
ax.tick_params(axis='y', labelsize=16)
ax.set_xlabel('', fontsize=18)
ax.set_ylabel('Accuracy (%)', fontsize=18)

# 设置网格线
ax.grid(True, which='both', linestyle='--', linewidth=0.6)

# --- 创建自定义图例 ---
# 创建图例元素
frama_c_line = mlines.Line2D([], [], color=(0.8,0,0), label='Frama-c', linewidth=2.5)
sygus_line = mlines.Line2D([], [], color=(0,0,0.8), label='syGus', linewidth=2.5)
solid_line = mlines.Line2D([], [], color='black', linestyle='solid', label='ASGSE', linewidth=2.5)
dashed_line = mlines.Line2D([], [], color='black', linestyle='dashed', label='AutoSpec', linewidth=2.5)

# 添加图例
ax.legend(handles=[frama_c_line, sygus_line, solid_line, dashed_line], fontsize=14)

# 显示图形
plt.show()
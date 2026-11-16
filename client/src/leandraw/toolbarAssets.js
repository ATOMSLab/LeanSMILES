const toolbarAssetModules = import.meta.glob('./assets/toolbar/*.png', {
  eager: true,
  import: 'default',
})

export const toolbarAssets = Object.fromEntries(
  Object.entries(toolbarAssetModules).map(([path, url]) => {
    const name = path.replace('./assets/toolbar/', '').replace('.png', '')
    return [name, url]
  })
)

export function toolbarAsset(name) {
  return toolbarAssets[name] || ''
}

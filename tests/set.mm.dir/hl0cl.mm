include "chlo.mm"
include "wcel.mm"
include "cnv.mm"
include "hlnv.mm"
include "nvzcl.mm"
include "syl.mm"

theorem hl0cl
  let cU: class U
  let cX: class X
  let cZ: class Z
  assume hl0cl.1: |- X = ( BaseSet ` U )
  assume hl0cl.5: |- Z = ( 0vec ` U )


  assert |- ( U e. CHilOLD -> Z e. X )

  proof
    cU
    chlo
    wcel
    cU
    cnv
    wcel
    cZ
    cX
    wcel
    cU
    hlnv
    cU
    cX
    cZ
    hl0cl.1
    hl0cl.5
    nvzcl
    syl
end

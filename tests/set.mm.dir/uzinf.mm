include "cz.mm"
include "wcel.mm"
include "cfn.mm"
include "com.mm"
include "ominf.mm"
include "cen.mm"
include "wbr.mm"
include "wb.mm"
include "uzenom.mm"
include "enfi.mm"
include "syl.mm"
include "mtbiri.mm"

theorem uzinf
  let cM: class M
  let cZ: class Z
  let vx: setvar x
  assume uzinf.1: |- Z = ( ZZ>= ` M )


  assert |- ( M e. ZZ -> -. Z e. Fin )

  proof
    cM
    cz
    wcel
    #
    cZ
    cfn
    wcel
    #
    com
    cfn
    wcel
    #
    ominf
    @0
    cZ
    com
    cen
    wbr
    @1
    @2
    wb
    cM
    cZ
    uzinf.1
    uzenom
    cZ
    com
    enfi
    syl
    mtbiri
end

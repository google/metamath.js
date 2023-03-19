include "cz.mm"
include "wcel.mm"
include "cmul.mm"
include "c1.mm"
include "csn.mm"
include "cxp.mm"
include "cseq.mm"
include "cli.mm"
include "wbr.mm"
include "prodfclim1.mm"
include "syl.mm"

theorem climprod1
  let wph: wff ph
  let cM: class M
  let cZ: class Z
  assume climprod1.1: |- Z = ( ZZ>= ` M )
  assume climprod1.2: |- ( ph -> M e. ZZ )


  assert |- ( ph -> seq M ( x. , ( Z X. { 1 } ) ) ~~> 1 )

  proof
    wph
    cM
    cz
    wcel
    cmul
    cZ
    c1
    csn
    cxp
    cM
    cseq
    c1
    cli
    wbr
    climprod1.2
    cM
    cZ
    climprod1.1
    prodfclim1
    syl
end

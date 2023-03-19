include "cdom.mm"
include "wbr.mm"
include "cen.mm"
include "acsmred.mm"
include "mrissd.mm"
include "acsdomd.mm"
include "cfv.mm"
include "eqcomd.mm"
include "acsinfd.mm"
include "sbth.mm"
include "syl2anc.mm"

theorem acsinfdimd
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cT: class T
  let cI: class I
  let cN: class N
  let cX: class X
  assume acsinfdimd.1: |- ( ph -> A e. ( ACS ` X ) )
  assume acsinfdimd.2: |- N = ( mrCls ` A )
  assume acsinfdimd.3: |- I = ( mrInd ` A )
  assume acsinfdimd.4: |- ( ph -> S e. I )
  assume acsinfdimd.5: |- ( ph -> T e. I )
  assume acsinfdimd.6: |- ( ph -> ( N ` S ) = ( N ` T ) )
  assume acsinfdimd.7: |- ( ph -> -. S e. Fin )


  assert |- ( ph -> S ~~ T )

  proof
    wph
    cS
    cT
    cdom
    wbr
    cT
    cS
    cdom
    wbr
    cS
    cT
    cen
    wbr
    wph
    cA
    cS
    cT
    cI
    cN
    cX
    acsinfdimd.1
    acsinfdimd.2
    acsinfdimd.3
    acsinfdimd.4
    wph
    cA
    cT
    cI
    cX
    acsinfdimd.3
    wph
    cA
    cX
    acsinfdimd.1
    acsmred
    #
    acsinfdimd.5
    mrissd
    #
    acsinfdimd.6
    acsinfdimd.7
    acsdomd
    wph
    cA
    cT
    cS
    cI
    cN
    cX
    acsinfdimd.1
    acsinfdimd.2
    acsinfdimd.3
    acsinfdimd.5
    wph
    cA
    cS
    cI
    cX
    acsinfdimd.3
    @0
    acsinfdimd.4
    mrissd
    wph
    cS
    cN
    cfv
    cT
    cN
    cfv
    acsinfdimd.6
    eqcomd
    wph
    cA
    cS
    cT
    cI
    cN
    cX
    acsinfdimd.1
    acsinfdimd.2
    acsinfdimd.3
    acsinfdimd.4
    @1
    acsinfdimd.6
    acsinfdimd.7
    acsinfd
    acsdomd
    cS
    cT
    sbth
    syl2anc
end

include "cvv.mm"
include "wcel.mm"
include "cupwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "w3a.mm"
include "wi.mm"
include "wa.mm"
include "cv.mm"
include "cdm.mm"
include "cword.mm"
include "cc0.mm"
include "chash.mm"
include "cfz.mm"
include "co.mm"
include "wf.mm"
include "c1.mm"
include "caddc.mm"
include "cpr.mm"
include "wceq.mm"
include "cfzo.mm"
include "wral.mm"
include "copab.mm"
include "upwlksfval.mm"
include "breqd.mm"
include "brabv.mm"
include "syl6bi.mm"
include "imdistani.mm"
include "3anass.mm"
include "sylibr.mm"
include "ex.mm"
include "wn.mm"
include "c0.mm"
include "fvprc.mm"
include "breq.mm"
include "br0.mm"
include "pm2.21i.mm"
include "syl.mm"
include "pm2.61i.mm"

theorem upwlkbprop
  let cP: class P
  let cF: class F
  let cG: class G
  let cI: class I
  let cV: class V
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let vp: setvar p
  let cW: class W
  let vx: setvar x
  assume upwlksfval.v: |- V = ( Vtx ` G )
  assume upwlksfval.i: |- I = ( iEdg ` G )


  assert |- ( F ( UPWalks ` G ) P -> ( G e. _V /\ F e. _V /\ P e. _V ) )

  proof
    cG
    cvv
    wcel
    #
    cF
    cP
    cG
    cupwlks
    cfv
    #
    wbr
    #
    @0
    cF
    cvv
    wcel
    #
    cP
    cvv
    wcel
    #
    w3a
    #
    wi
    #
    @0
    @2
    @5
    @0
    @2
    wa
    @0
    @3
    @4
    wa
    #
    wa
    @5
    @0
    @2
    @7
    @0
    @2
    cF
    cP
    vf
    cv
    #
    cI
    cdm
    cword
    wcel
    cc0
    @8
    chash
    cfv
    #
    cfz
    co
    cV
    vp
    cv
    #
    wf
    vk
    cv
    #
    @8
    cfv
    cI
    cfv
    @11
    @10
    cfv
    @11
    c1
    caddc
    co
    @10
    cfv
    cpr
    wceq
    vk
    cc0
    @9
    cfzo
    co
    wral
    w3a
    #
    vf
    vp
    copab
    #
    wbr
    @7
    @0
    @1
    @13
    cF
    cP
    vf
    vk
    cG
    cI
    cV
    cvv
    vp
    upwlksfval.v
    upwlksfval.i
    upwlksfval
    breqd
    @12
    vf
    vp
    cF
    cP
    brabv
    syl6bi
    imdistani
    @0
    @3
    @4
    3anass
    sylibr
    ex
    @0
    wn
    @1
    c0
    wceq
    #
    @6
    cG
    cupwlks
    fvprc
    @14
    @2
    cF
    cP
    c0
    wbr
    #
    @5
    cF
    cP
    @1
    c0
    breq
    @15
    @5
    cF
    cP
    br0
    pm2.21i
    syl6bi
    syl
    pm2.61i
end

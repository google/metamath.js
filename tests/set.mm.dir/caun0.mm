include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cca.mm"
include "wa.mm"
include "cv.mm"
include "cdm.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "cuz.mm"
include "wral.mm"
include "cz.mm"
include "wrex.mm"
include "crp.mm"
include "c0.mm"
include "wne.mm"
include "c1.mm"
include "1rp.mm"
include "ne0ii.mm"
include "cc.mm"
include "cpm.mm"
include "iscau2.mm"
include "simplbda.mm"
include "r19.2z.mm"
include "sylancr.mm"
include "wi.mm"
include "uzid.mm"
include "ne0i.mm"
include "ex.mm"
include "3syl.mm"
include "3ad2ant2.mm"
include "rexlimivw.mm"
include "syl6.mm"
include "rexlimiv.mm"
include "syl.mm"

theorem caun0
  let cD: class D
  let cF: class F
  let cX: class X
  let vj: setvar j
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( D e. ( *Met ` X ) /\ F e. ( Cau ` D ) ) -> X =/= (/) )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cF
    cD
    cca
    cfv
    wcel
    #
    wa
    #
    vk
    cv
    #
    cF
    cdm
    wcel
    #
    @3
    cF
    cfv
    #
    cX
    wcel
    #
    @5
    vj
    cv
    #
    cF
    cfv
    cD
    co
    vx
    cv
    clt
    wbr
    #
    w3a
    #
    vk
    @7
    cuz
    cfv
    #
    wral
    #
    vj
    cz
    wrex
    #
    vx
    crp
    wrex
    #
    cX
    c0
    wne
    #
    @2
    crp
    c0
    wne
    @12
    vx
    crp
    wral
    #
    @13
    c1
    crp
    1rp
    ne0ii
    @0
    @1
    cF
    cX
    cc
    cpm
    co
    wcel
    @15
    vx
    cD
    vj
    vk
    cF
    cX
    iscau2
    simplbda
    @12
    vx
    crp
    r19.2z
    sylancr
    @12
    @14
    vx
    crp
    @11
    @14
    vj
    cz
    @7
    cz
    wcel
    #
    @11
    @9
    vk
    @10
    wrex
    #
    @14
    @16
    @7
    @10
    wcel
    @10
    c0
    wne
    #
    @11
    @17
    wi
    @7
    uzid
    @10
    @7
    ne0i
    @18
    @11
    @17
    @9
    vk
    @10
    r19.2z
    ex
    3syl
    @9
    @14
    vk
    @10
    @6
    @4
    @14
    @8
    cX
    @5
    ne0i
    3ad2ant2
    rexlimivw
    syl6
    rexlimiv
    rexlimivw
    syl
end

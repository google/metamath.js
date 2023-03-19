include "cn.mm"
include "wcel.mm"
include "ciccp.mm"
include "cfv.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "cxr.mm"
include "cfz.mm"
include "cmap.mm"
include "c1.mm"
include "caddc.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "wral.mm"
include "wi.mm"
include "iccpart.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "breq12d.mm"
include "rspcva.mm"
include "expcom.mm"
include "adantl.mm"
include "simpl.mm"
include "jctild.mm"
include "syl6bi.mm"
include "3imp.mm"

theorem iccpartimp
  let cP: class P
  let cI: class I
  let cM: class M
  let vi: setvar i
  let vm: setvar m
  let vp: setvar p
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( M e. NN /\ P e. ( RePart ` M ) /\ I e. ( 0 ..^ M ) ) -> ( P e. ( RR* ^m ( 0 ... M ) ) /\ ( P ` I ) < ( P ` ( I + 1 ) ) ) )

  proof
    cM
    cn
    wcel
    #
    cP
    cM
    ciccp
    cfv
    wcel
    #
    cI
    cc0
    cM
    cfzo
    co
    #
    wcel
    #
    cP
    cxr
    cc0
    cM
    cfz
    co
    cmap
    co
    wcel
    #
    cI
    cP
    cfv
    #
    cI
    c1
    caddc
    co
    #
    cP
    cfv
    #
    clt
    wbr
    #
    wa
    #
    @0
    @1
    @4
    vi
    cv
    #
    cP
    cfv
    #
    @10
    c1
    caddc
    co
    #
    cP
    cfv
    #
    clt
    wbr
    #
    vi
    @2
    wral
    #
    wa
    #
    @3
    @9
    wi
    cP
    vi
    cM
    iccpart
    @16
    @3
    @8
    @4
    @15
    @3
    @8
    wi
    @4
    @3
    @15
    @8
    @14
    @8
    vi
    cI
    @2
    @10
    cI
    wceq
    #
    @11
    @5
    @13
    @7
    clt
    @10
    cI
    cP
    fveq2
    @17
    @12
    @6
    cP
    @10
    cI
    c1
    caddc
    oveq1
    fveq2d
    breq12d
    rspcva
    expcom
    adantl
    @4
    @15
    simpl
    jctild
    syl6bi
    3imp
end

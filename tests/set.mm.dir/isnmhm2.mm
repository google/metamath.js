include "cnlm.mm"
include "wcel.mm"
include "clmhm.mm"
include "co.mm"
include "cnmhm.mm"
include "cfv.mm"
include "cr.mm"
include "wb.mm"
include "wa.mm"
include "cnghm.mm"
include "isnmhm.mm"
include "baib.mm"
include "baibd.mm"
include "cghm.mm"
include "lmghm.mm"
include "cngp.mm"
include "nlmngp.mm"
include "isnghm.mm"
include "syl2an.mm"
include "sylan2.mm"
include "bitrd.mm"
include "3impa.mm"

theorem isnmhm2
  let cS: class S
  let cT: class T
  let cF: class F
  let cN: class N
  let vs: setvar s
  let vt: setvar t
  assume isnmhm2.1: |- N = ( S normOp T )


  assert |- ( ( S e. NrmMod /\ T e. NrmMod /\ F e. ( S LMHom T ) ) -> ( F e. ( S NMHom T ) <-> ( N ` F ) e. RR ) )

  proof
    cS
    cnlm
    wcel
    #
    cT
    cnlm
    wcel
    #
    cF
    cS
    cT
    clmhm
    co
    wcel
    #
    cF
    cS
    cT
    cnmhm
    co
    wcel
    #
    cF
    cN
    cfv
    cr
    wcel
    #
    wb
    @0
    @1
    wa
    #
    @2
    wa
    @3
    cF
    cS
    cT
    cnghm
    co
    wcel
    #
    @4
    @5
    @3
    @2
    @6
    @3
    @5
    @2
    @6
    wa
    cS
    cT
    cF
    isnmhm
    baib
    baibd
    @2
    @5
    cF
    cS
    cT
    cghm
    co
    wcel
    #
    @6
    @4
    wb
    cS
    cT
    cF
    lmghm
    @5
    @6
    @7
    @4
    @0
    cS
    cngp
    wcel
    #
    cT
    cngp
    wcel
    #
    @6
    @7
    @4
    wa
    #
    wb
    @1
    cS
    nlmngp
    cT
    nlmngp
    @6
    @8
    @9
    wa
    @10
    cS
    cT
    cF
    cN
    isnmhm2.1
    isnghm
    baib
    syl2an
    baibd
    sylan2
    bitrd
    3impa
end

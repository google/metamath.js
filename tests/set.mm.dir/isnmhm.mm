include "cnmhm.mm"
include "co.mm"
include "wcel.mm"
include "cnlm.mm"
include "wa.mm"
include "clmhm.mm"
include "cnghm.mm"
include "cv.mm"
include "cin.mm"
include "df-nmhm.mm"
include "elmpt2cl.mm"
include "wceq.mm"
include "oveq12.mm"
include "ineq12d.mm"
include "ovex.mm"
include "inex1.mm"
include "ovmpt2a.mm"
include "eleq2d.mm"
include "elin.mm"
include "syl6bb.mm"
include "biadan2.mm"

theorem isnmhm
  let cS: class S
  let cT: class T
  let cF: class F
  let vs: setvar s
  let vt: setvar t


  assert |- ( F e. ( S NMHom T ) <-> ( ( S e. NrmMod /\ T e. NrmMod ) /\ ( F e. ( S LMHom T ) /\ F e. ( S NGHom T ) ) ) )

  proof
    cF
    cS
    cT
    cnmhm
    co
    #
    wcel
    #
    cS
    cnlm
    wcel
    cT
    cnlm
    wcel
    wa
    #
    cF
    cS
    cT
    clmhm
    co
    #
    wcel
    cF
    cS
    cT
    cnghm
    co
    #
    wcel
    wa
    #
    vs
    vt
    cnlm
    cnlm
    vs
    cv
    #
    vt
    cv
    #
    clmhm
    co
    #
    @6
    @7
    cnghm
    co
    #
    cin
    #
    cS
    cT
    cnmhm
    cF
    vt
    vs
    df-nmhm
    #
    elmpt2cl
    @2
    @1
    cF
    @3
    @4
    cin
    #
    wcel
    @5
    @2
    @0
    @12
    cF
    vs
    vt
    cS
    cT
    cnlm
    cnlm
    @10
    @12
    cnmhm
    @6
    cS
    wceq
    @7
    cT
    wceq
    wa
    @8
    @3
    @9
    @4
    @6
    cS
    @7
    cT
    clmhm
    oveq12
    @6
    cS
    @7
    cT
    cnghm
    oveq12
    ineq12d
    @11
    @3
    @4
    cS
    cT
    clmhm
    ovex
    inex1
    ovmpt2a
    eleq2d
    cF
    @3
    @4
    elin
    syl6bb
    biadan2
end

include "cword.mm"
include "wcel.mm"
include "wa.mm"
include "cconcat.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "c0.mm"
include "wb.mm"
include "ccatcl.mm"
include "hasheq0.mm"
include "syl.mm"
include "caddc.mm"
include "ccatlen.mm"
include "eqeq1d.mm"
include "cr.mm"
include "cle.mm"
include "wbr.mm"
include "cn0.mm"
include "lencl.mm"
include "nn0re.mm"
include "nn0ge0.mm"
include "jca.mm"
include "add20.mm"
include "syl2an.mm"
include "bi2anan9.mm"
include "3bitrd.mm"
include "bitr3d.mm"

theorem ccat0
  let cB: class B
  let cS: class S
  let cT: class T
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x


  assert |- ( ( S e. Word B /\ T e. Word B ) -> ( ( S ++ T ) = (/) <-> ( S = (/) /\ T = (/) ) ) )

  proof
    cS
    cB
    cword
    #
    wcel
    #
    cT
    @0
    wcel
    #
    wa
    #
    cS
    cT
    cconcat
    co
    #
    chash
    cfv
    #
    cc0
    wceq
    #
    @4
    c0
    wceq
    #
    cS
    c0
    wceq
    #
    cT
    c0
    wceq
    #
    wa
    #
    @3
    @4
    @0
    wcel
    @6
    @7
    wb
    cB
    cS
    cT
    ccatcl
    @4
    @0
    hasheq0
    syl
    @3
    @6
    cS
    chash
    cfv
    #
    cT
    chash
    cfv
    #
    caddc
    co
    #
    cc0
    wceq
    #
    @11
    cc0
    wceq
    #
    @12
    cc0
    wceq
    #
    wa
    #
    @10
    @3
    @5
    @13
    cc0
    cB
    cS
    cT
    ccatlen
    eqeq1d
    @1
    @11
    cr
    wcel
    #
    cc0
    @11
    cle
    wbr
    #
    wa
    #
    @12
    cr
    wcel
    #
    cc0
    @12
    cle
    wbr
    #
    wa
    #
    @14
    @17
    wb
    @2
    @1
    @11
    cn0
    wcel
    #
    @20
    cB
    cS
    lencl
    @24
    @18
    @19
    @11
    nn0re
    @11
    nn0ge0
    jca
    syl
    @2
    @12
    cn0
    wcel
    #
    @23
    cB
    cT
    lencl
    @25
    @21
    @22
    @12
    nn0re
    @12
    nn0ge0
    jca
    syl
    @11
    @12
    add20
    syl2an
    @1
    @15
    @8
    @2
    @16
    @9
    cS
    @0
    hasheq0
    cT
    @0
    hasheq0
    bi2anan9
    3bitrd
    bitr3d
end

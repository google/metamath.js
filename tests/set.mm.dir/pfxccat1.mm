include "cword.mm"
include "wcel.mm"
include "wa.mm"
include "cconcat.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "cpfx.mm"
include "cc0.mm"
include "cfzo.mm"
include "cres.mm"
include "cfz.mm"
include "wceq.mm"
include "ccatcl.mm"
include "caddc.mm"
include "cn0.mm"
include "lencl.mm"
include "anim12i.mm"
include "nn0fz0.mm"
include "sylib.mm"
include "adantr.mm"
include "elfz0add.mm"
include "sylc.mm"
include "ccatlen.mm"
include "oveq2d.mm"
include "eleqtrrd.mm"
include "pfxres.mm"
include "syl2anc.mm"
include "wfn.mm"
include "wss.mm"
include "ccatvalfn.mm"
include "cuz.mm"
include "cz.mm"
include "nn0zd.mm"
include "uzid.mm"
include "syl.mm"
include "uzaddcl.mm"
include "syl2an.mm"
include "fzoss2.mm"
include "fnssres.mm"
include "wrdfn.mm"
include "cv.mm"
include "fvres.mm"
include "adantl.mm"
include "ccatval1.mm"
include "3expa.mm"
include "eqtrd.mm"
include "eqfnfvd.mm"

theorem pfxccat1
  let cB: class B
  let cS: class S
  let cT: class T
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( S e. Word B /\ T e. Word B ) -> ( ( S ++ T ) prefix ( # ` S ) ) = S )

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
    cS
    chash
    cfv
    #
    cpfx
    co
    #
    @4
    cc0
    @5
    cfzo
    co
    #
    cres
    #
    cS
    @3
    @4
    @0
    wcel
    @5
    cc0
    @4
    chash
    cfv
    #
    cfz
    co
    #
    wcel
    @6
    @8
    wceq
    cB
    cS
    cT
    ccatcl
    @3
    @5
    cc0
    @5
    cT
    chash
    cfv
    #
    caddc
    co
    #
    cfz
    co
    #
    @10
    @3
    @5
    cn0
    wcel
    #
    @11
    cn0
    wcel
    #
    wa
    @5
    cc0
    @5
    cfz
    co
    wcel
    #
    @5
    @13
    wcel
    @1
    @14
    @2
    @15
    cB
    cS
    lencl
    #
    cB
    cT
    lencl
    #
    anim12i
    @1
    @16
    @2
    @1
    @14
    @16
    @17
    @5
    nn0fz0
    sylib
    adantr
    @5
    @11
    @5
    elfz0add
    sylc
    @3
    @9
    @12
    cc0
    cfz
    cB
    cS
    cT
    ccatlen
    oveq2d
    eleqtrrd
    cB
    @4
    @5
    pfxres
    syl2anc
    @3
    vk
    @7
    @8
    cS
    @3
    @4
    cc0
    @12
    cfzo
    co
    #
    wfn
    @7
    @19
    wss
    #
    @8
    @7
    wfn
    cS
    cT
    cB
    ccatvalfn
    @3
    @12
    @5
    cuz
    cfv
    #
    wcel
    #
    @20
    @1
    @5
    @21
    wcel
    #
    @15
    @22
    @2
    @1
    @5
    cz
    wcel
    @23
    @1
    @5
    @17
    nn0zd
    @5
    uzid
    syl
    @18
    @11
    @5
    @5
    uzaddcl
    syl2an
    @5
    cc0
    @12
    fzoss2
    syl
    @19
    @7
    @4
    fnssres
    syl2anc
    @1
    cS
    @7
    wfn
    @2
    cB
    cS
    wrdfn
    adantr
    @3
    vk
    cv
    #
    @7
    wcel
    #
    wa
    @24
    @8
    cfv
    #
    @24
    @4
    cfv
    #
    @24
    cS
    cfv
    #
    @25
    @26
    @27
    wceq
    @3
    @24
    @7
    @4
    fvres
    adantl
    @1
    @2
    @25
    @27
    @28
    wceq
    cB
    cS
    cT
    @24
    ccatval1
    3expa
    eqtrd
    eqfnfvd
    eqtrd
end

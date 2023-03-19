include "cword.mm"
include "wcel.mm"
include "wa.mm"
include "cconcat.mm"
include "co.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cop.mm"
include "csubstr.mm"
include "cfzo.mm"
include "cres.mm"
include "cfz.mm"
include "wceq.mm"
include "ccatcl.mm"
include "cuz.mm"
include "cn0.mm"
include "lencl.mm"
include "adantr.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "caddc.mm"
include "ccatlen.mm"
include "cz.mm"
include "nn0zd.mm"
include "uzid.mm"
include "syl.mm"
include "adantl.mm"
include "uzaddcl.mm"
include "syl2anc.mm"
include "eqeltrd.mm"
include "elfzuzb.mm"
include "sylanbrc.mm"
include "swrd0val.mm"
include "wfn.mm"
include "wss.mm"
include "wf.mm"
include "wrdf.mm"
include "ffn.mm"
include "3syl.mm"
include "fzoss2.mm"
include "fnssres.mm"
include "cv.mm"
include "fvres.mm"
include "ccatval1.mm"
include "3expa.mm"
include "eqtrd.mm"
include "eqfnfvd.mm"

theorem swrdccat1
  let cB: class B
  let cS: class S
  let cT: class T
  let vk: setvar k


  assert |- ( ( S e. Word B /\ T e. Word B ) -> ( ( S ++ T ) substr <. 0 , ( # ` S ) >. ) = S )

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
    cc0
    cS
    chash
    cfv
    #
    cop
    csubstr
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
    #
    @5
    cc0
    @4
    chash
    cfv
    #
    cfz
    co
    wcel
    #
    @6
    @8
    wceq
    cB
    cS
    cT
    ccatcl
    #
    @3
    @5
    cc0
    cuz
    cfv
    #
    wcel
    @10
    @5
    cuz
    cfv
    #
    wcel
    #
    @11
    @3
    @5
    cn0
    @13
    @1
    @5
    cn0
    wcel
    @2
    cB
    cS
    lencl
    adantr
    #
    nn0uz
    syl6eleq
    @3
    @10
    @5
    cT
    chash
    cfv
    #
    caddc
    co
    #
    @14
    cB
    cS
    cT
    ccatlen
    @3
    @5
    @14
    wcel
    #
    @17
    cn0
    wcel
    #
    @18
    @14
    wcel
    @3
    @5
    cz
    wcel
    @19
    @3
    @5
    @16
    nn0zd
    @5
    uzid
    syl
    @2
    @20
    @1
    cB
    cT
    lencl
    adantl
    @17
    @5
    @5
    uzaddcl
    syl2anc
    eqeltrd
    #
    @5
    cc0
    @10
    elfzuzb
    sylanbrc
    cB
    @4
    @5
    swrd0val
    syl2anc
    @3
    vk
    @7
    @8
    cS
    @3
    @4
    cc0
    @10
    cfzo
    co
    #
    wfn
    #
    @7
    @22
    wss
    #
    @8
    @7
    wfn
    @3
    @9
    @22
    cB
    @4
    wf
    @23
    @12
    cB
    @4
    wrdf
    @22
    cB
    @4
    ffn
    3syl
    @3
    @15
    @24
    @21
    @5
    cc0
    @10
    fzoss2
    syl
    @22
    @7
    @4
    fnssres
    syl2anc
    @3
    @7
    cB
    cS
    wf
    #
    cS
    @7
    wfn
    @1
    @25
    @2
    cB
    cS
    wrdf
    adantr
    @7
    cB
    cS
    ffn
    syl
    @3
    vk
    cv
    #
    @7
    wcel
    #
    wa
    @26
    @8
    cfv
    #
    @26
    @4
    cfv
    #
    @26
    cS
    cfv
    #
    @27
    @28
    @29
    wceq
    @3
    @26
    @7
    @4
    fvres
    adantl
    @1
    @2
    @27
    @29
    @30
    wceq
    cB
    cS
    cT
    @26
    ccatval1
    3expa
    eqtrd
    eqfnfvd
    eqtrd
end

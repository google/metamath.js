include "cword.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "co.mm"
include "cconcat.mm"
include "caddc.mm"
include "cop.mm"
include "csubstr.mm"
include "wfn.mm"
include "wf.mm"
include "ccatcl.mm"
include "swrdcl.mm"
include "wrdf.mm"
include "ffn.mm"
include "4syl.mm"
include "cmin.mm"
include "cfz.mm"
include "wceq.mm"
include "cuz.mm"
include "cn0.mm"
include "lencl.mm"
include "adantr.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "cz.mm"
include "nn0zd.mm"
include "uzid.mm"
include "syl.mm"
include "adantl.mm"
include "uzaddcl.mm"
include "syl2anc.mm"
include "elfzuzb.mm"
include "sylanbrc.mm"
include "nn0addcld.mm"
include "ccatlen.mm"
include "oveq2d.mm"
include "eleqtrrd.mm"
include "swrdlen.mm"
include "syl3anc.mm"
include "nn0cnd.mm"
include "pncan2d.mm"
include "eqtrd.mm"
include "fneq2d.mm"
include "mpbid.mm"
include "cv.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "swrdfv.mm"
include "syl31anc.mm"
include "ccatval3.mm"
include "3expa.mm"
include "eqfnfvd.mm"

theorem swrdccat2
  let cB: class B
  let cS: class S
  let cT: class T
  let vk: setvar k


  assert |- ( ( S e. Word B /\ T e. Word B ) -> ( ( S ++ T ) substr <. ( # ` S ) , ( ( # ` S ) + ( # ` T ) ) >. ) = T )

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
    vk
    cc0
    cT
    chash
    cfv
    #
    cfzo
    co
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
    @7
    @4
    caddc
    co
    #
    cop
    csubstr
    co
    #
    cT
    @3
    @9
    cc0
    @9
    chash
    cfv
    #
    cfzo
    co
    #
    wfn
    #
    @9
    @5
    wfn
    @3
    @6
    @0
    wcel
    #
    @9
    @0
    wcel
    @11
    cB
    @9
    wf
    @12
    cB
    cS
    cT
    ccatcl
    #
    cB
    @6
    @7
    @8
    swrdcl
    cB
    @9
    wrdf
    @11
    cB
    @9
    ffn
    4syl
    @3
    @11
    @5
    @9
    @3
    @10
    @4
    cc0
    cfzo
    @3
    @10
    @8
    @7
    cmin
    co
    #
    @4
    @3
    @13
    @7
    cc0
    @8
    cfz
    co
    #
    wcel
    #
    @8
    cc0
    @6
    chash
    cfv
    #
    cfz
    co
    #
    wcel
    #
    @10
    @15
    wceq
    @14
    @3
    @7
    cc0
    cuz
    cfv
    #
    wcel
    @8
    @7
    cuz
    cfv
    #
    wcel
    #
    @17
    @3
    @7
    cn0
    @21
    @1
    @7
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
    @7
    @22
    wcel
    #
    @4
    cn0
    wcel
    #
    @23
    @3
    @7
    cz
    wcel
    @25
    @3
    @7
    @24
    nn0zd
    @7
    uzid
    syl
    @2
    @26
    @1
    cB
    cT
    lencl
    adantl
    #
    @4
    @7
    @7
    uzaddcl
    syl2anc
    @7
    cc0
    @8
    elfzuzb
    sylanbrc
    #
    @3
    @8
    @16
    @19
    @3
    @8
    @21
    wcel
    @8
    @8
    cuz
    cfv
    wcel
    #
    @8
    @16
    wcel
    @3
    @8
    cn0
    @21
    @3
    @7
    @4
    @24
    @27
    nn0addcld
    #
    nn0uz
    syl6eleq
    @3
    @8
    cz
    wcel
    @29
    @3
    @8
    @30
    nn0zd
    @8
    uzid
    syl
    @8
    cc0
    @8
    elfzuzb
    sylanbrc
    @3
    @18
    @8
    cc0
    cfz
    cB
    cS
    cT
    ccatlen
    oveq2d
    eleqtrrd
    #
    cB
    @6
    @7
    @8
    swrdlen
    syl3anc
    @3
    @7
    @4
    @3
    @7
    @24
    nn0cnd
    @3
    @4
    @27
    nn0cnd
    pncan2d
    #
    eqtrd
    oveq2d
    fneq2d
    mpbid
    @3
    @5
    cB
    cT
    wf
    #
    cT
    @5
    wfn
    @2
    @33
    @1
    cB
    cT
    wrdf
    adantl
    @5
    cB
    cT
    ffn
    syl
    @3
    vk
    cv
    #
    @5
    wcel
    #
    wa
    #
    @34
    @9
    cfv
    #
    @34
    @7
    caddc
    co
    @6
    cfv
    #
    @34
    cT
    cfv
    #
    @36
    @13
    @17
    @20
    @34
    cc0
    @15
    cfzo
    co
    #
    wcel
    #
    @37
    @38
    wceq
    @3
    @13
    @35
    @14
    adantr
    @3
    @17
    @35
    @28
    adantr
    @3
    @20
    @35
    @31
    adantr
    @3
    @41
    @35
    @3
    @40
    @5
    @34
    @3
    @15
    @4
    cc0
    cfzo
    @32
    oveq2d
    eleq2d
    biimpar
    cB
    @6
    @7
    @8
    @34
    swrdfv
    syl31anc
    @1
    @2
    @35
    @38
    @39
    wceq
    cB
    cS
    cT
    @34
    ccatval3
    3expa
    eqtrd
    eqfnfvd
end

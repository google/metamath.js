include "cnv.mm"
include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "c1.mm"
include "cneg.mm"
include "cle.mm"
include "wbr.mm"
include "nvdif.mm"
include "negeqd.mm"
include "cr.mm"
include "nvcl.mm"
include "3adant2.mm"
include "3adant3.mm"
include "simp1.mm"
include "cc.mm"
include "neg1cn.mm"
include "nvscl.mm"
include "mp3an2.mm"
include "nvgcl.mm"
include "syld3an3.mm"
include "3com23.mm"
include "syl2anc.mm"
include "renegcld.mm"
include "caddc.mm"
include "wceq.mm"
include "nvcom.mm"
include "cn0v.mm"
include "wa.mm"
include "simprr.mm"
include "adantrr.mm"
include "simprl.mm"
include "3jca.mm"
include "nvass.mm"
include "syldan.mm"
include "3impb.mm"
include "eqid.mm"
include "nvlinv.mm"
include "oveq2d.mm"
include "nv0rid.mm"
include "3eqtrd.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "nvtri.mm"
include "eqbrtrrd.mm"
include "recnd.mm"
include "subnegd.mm"
include "breqtrrd.mm"
include "lesubd.mm"
include "eqbrtrd.mm"
include "simp2.mm"
include "simp3.mm"
include "syl13anc.mm"
include "syld3an2.mm"
include "lesubaddd.mm"
include "mpbird.mm"
include "resubcld.mm"
include "absled.mm"
include "mpbir2and.mm"

theorem nvabs
  let cA: class A
  let cB: class B
  let cS: class S
  let cU: class U
  let cG: class G
  let cN: class N
  let cX: class X
  assume nvabs.1: |- X = ( BaseSet ` U )
  assume nvabs.2: |- G = ( +v ` U )
  assume nvabs.4: |- S = ( .sOLD ` U )
  assume nvabs.6: |- N = ( normCV ` U )


  assert |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) -> ( abs ` ( ( N ` A ) - ( N ` B ) ) ) <_ ( N ` ( A G ( -u 1 S B ) ) ) )

  proof
    cU
    cnv
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    w3a
    #
    cA
    cN
    cfv
    #
    cB
    cN
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    cA
    c1
    cneg
    #
    cB
    cS
    co
    #
    cG
    co
    #
    cN
    cfv
    #
    cle
    wbr
    @10
    cneg
    #
    @6
    cle
    wbr
    @6
    @10
    cle
    wbr
    #
    @3
    @11
    cB
    @7
    cA
    cS
    co
    #
    cG
    co
    #
    cN
    cfv
    #
    cneg
    #
    @6
    cle
    @3
    @10
    @15
    cA
    cB
    cS
    cU
    cG
    cN
    cX
    nvabs.1
    nvabs.2
    nvabs.4
    nvabs.6
    nvdif
    negeqd
    @3
    @5
    @4
    @16
    @0
    @2
    @5
    cr
    wcel
    @1
    cB
    cU
    cN
    cX
    nvabs.1
    nvabs.6
    nvcl
    3adant2
    #
    @0
    @1
    @4
    cr
    wcel
    @2
    cA
    cU
    cN
    cX
    nvabs.1
    nvabs.6
    nvcl
    3adant3
    #
    @3
    @15
    @3
    @0
    @14
    cX
    wcel
    #
    @15
    cr
    wcel
    @0
    @1
    @2
    simp1
    #
    @0
    @2
    @1
    @19
    @0
    @2
    @1
    @13
    cX
    wcel
    #
    @19
    @0
    @1
    @21
    @2
    @0
    @7
    cc
    wcel
    #
    @1
    @21
    neg1cn
    @7
    cA
    cS
    cU
    cX
    nvabs.1
    nvabs.4
    nvscl
    mp3an2
    #
    3adant2
    cB
    @13
    cU
    cG
    cX
    nvabs.1
    nvabs.2
    nvgcl
    syld3an3
    3com23
    #
    @14
    cU
    cN
    cX
    nvabs.1
    nvabs.6
    nvcl
    syl2anc
    #
    renegcld
    @3
    @5
    @4
    @15
    caddc
    co
    #
    @4
    @16
    cmin
    co
    cle
    @3
    cA
    @14
    cG
    co
    #
    cN
    cfv
    #
    @5
    @26
    cle
    @3
    @27
    cB
    cN
    @3
    @27
    @14
    cA
    cG
    co
    #
    cB
    @0
    @1
    @2
    @19
    @27
    @29
    wceq
    @24
    cA
    @14
    cU
    cG
    cX
    nvabs.1
    nvabs.2
    nvcom
    syld3an3
    @3
    @29
    cB
    @13
    cA
    cG
    co
    #
    cG
    co
    #
    cB
    cU
    cn0v
    cfv
    #
    cG
    co
    #
    cB
    @0
    @1
    @2
    @29
    @31
    wceq
    #
    @0
    @1
    @2
    wa
    #
    @2
    @21
    @1
    w3a
    @34
    @0
    @35
    wa
    @2
    @21
    @1
    @0
    @1
    @2
    simprr
    @0
    @1
    @21
    @2
    @23
    adantrr
    @0
    @1
    @2
    simprl
    3jca
    cB
    @13
    cA
    cU
    cG
    cX
    nvabs.1
    nvabs.2
    nvass
    syldan
    3impb
    @3
    @30
    @32
    cB
    cG
    @0
    @1
    @30
    @32
    wceq
    @2
    cA
    cS
    cU
    cG
    cX
    @32
    nvabs.1
    nvabs.2
    nvabs.4
    @32
    eqid
    #
    nvlinv
    3adant3
    oveq2d
    @0
    @2
    @33
    cB
    wceq
    @1
    cB
    cU
    cG
    cX
    @32
    nvabs.1
    nvabs.2
    @36
    nv0rid
    3adant2
    3eqtrd
    eqtrd
    fveq2d
    @0
    @1
    @2
    @19
    @28
    @26
    cle
    wbr
    @24
    cA
    @14
    cU
    cG
    cN
    cX
    nvabs.1
    nvabs.2
    nvabs.6
    nvtri
    syld3an3
    eqbrtrrd
    @3
    @4
    @15
    @3
    @4
    @18
    recnd
    @3
    @15
    @25
    recnd
    subnegd
    breqtrrd
    lesubd
    eqbrtrd
    @3
    @12
    @4
    @10
    @5
    caddc
    co
    #
    cle
    wbr
    @3
    @9
    cB
    cG
    co
    #
    cN
    cfv
    #
    @4
    @37
    cle
    @3
    @38
    cA
    cN
    @3
    @38
    cA
    @8
    cB
    cG
    co
    #
    cG
    co
    #
    cA
    @32
    cG
    co
    #
    cA
    @3
    @0
    @1
    @8
    cX
    wcel
    #
    @2
    @38
    @41
    wceq
    @20
    @0
    @1
    @2
    simp2
    @0
    @2
    @43
    @1
    @0
    @22
    @2
    @43
    neg1cn
    @7
    cB
    cS
    cU
    cX
    nvabs.1
    nvabs.4
    nvscl
    mp3an2
    3adant2
    #
    @0
    @1
    @2
    simp3
    cA
    @8
    cB
    cU
    cG
    cX
    nvabs.1
    nvabs.2
    nvass
    syl13anc
    @3
    @40
    @32
    cA
    cG
    @0
    @2
    @40
    @32
    wceq
    @1
    cB
    cS
    cU
    cG
    cX
    @32
    nvabs.1
    nvabs.2
    nvabs.4
    @36
    nvlinv
    3adant2
    oveq2d
    @0
    @1
    @42
    cA
    wceq
    @2
    cA
    cU
    cG
    cX
    @32
    nvabs.1
    nvabs.2
    @36
    nv0rid
    3adant3
    3eqtrd
    fveq2d
    @0
    @9
    cX
    wcel
    #
    @1
    @2
    @39
    @37
    cle
    wbr
    @0
    @1
    @2
    @43
    @45
    @44
    cA
    @8
    cU
    cG
    cX
    nvabs.1
    nvabs.2
    nvgcl
    syld3an3
    #
    @9
    cB
    cU
    cG
    cN
    cX
    nvabs.1
    nvabs.2
    nvabs.6
    nvtri
    syld3an2
    eqbrtrrd
    @3
    @4
    @5
    @10
    @18
    @17
    @3
    @0
    @45
    @10
    cr
    wcel
    @20
    @46
    @9
    cU
    cN
    cX
    nvabs.1
    nvabs.6
    nvcl
    syl2anc
    #
    lesubaddd
    mpbird
    @3
    @6
    @10
    @3
    @4
    @5
    @18
    @17
    resubcld
    @47
    absled
    mpbir2and
end

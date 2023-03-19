include "cn0.mm"
include "cmap.mm"
include "co.mm"
include "wss.mm"
include "cfn.mm"
include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "cfsupp.mm"
include "wbr.mm"
include "wral.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "csupp.mm"
include "cc0.mm"
include "cfz.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfan.mm"
include "cle.mm"
include "wi.mm"
include "cdm.mm"
include "suppssdm.mm"
include "wfn.mm"
include "ssel2.mm"
include "elmapfn.mm"
include "wceq.mm"
include "fndm.mm"
include "eqimss.mm"
include "syl.mm"
include "3syl.mm"
include "3ad2antl1.mm"
include "syl5ss.mm"
include "sseld.mm"
include "adantlr.mm"
include "imp.mm"
include "fsuppmapnn0fiublem.mm"
include "ad2antrr.mm"
include "ciun.mm"
include "cr.mm"
include "ex.mm"
include "3ad2ant1.mm"
include "adantr.mm"
include "nn0ssre.mm"
include "syl6eqss.mm"
include "ralrimi.mm"
include "iunss.mm"
include "sylibr.mm"
include "syl5eqss.mm"
include "simp2.mm"
include "id.mm"
include "fsuppimpd.mm"
include "ralimi.mm"
include "anim12i.mm"
include "iunfi.mm"
include "syl5eqel.mm"
include "wrex.mm"
include "rspe.mm"
include "eliun.mm"
include "syl6eleqr.mm"
include "adantll.mm"
include "clt.mm"
include "csup.mm"
include "a1i.mm"
include "supfirege.mm"
include "elfz2nn0.mm"
include "syl3anbrc.mm"
include "ssrdv.mm"

theorem fsuppmapnn0fiub
  let cR: class R
  let cS: class S
  let cU: class U
  let vf: setvar f
  let cM: class M
  let cV: class V
  let cZ: class Z
  let vx: setvar x
  assume fsuppmapnn0fiub.u: |- U = U_ f e. M ( f supp Z )
  assume fsuppmapnn0fiub.s: |- S = sup ( U , RR , < )

  disjoint M f
  disjoint R f
  disjoint U f
  disjoint V f
  disjoint Z f
  disjoint M x
  disjoint f x
  disjoint R x
  disjoint S x
  disjoint U x
  disjoint V x
  disjoint Z x
  assert |- ( ( M C_ ( R ^m NN0 ) /\ M e. Fin /\ Z e. V ) -> ( ( A. f e. M f finSupp Z /\ U =/= (/) ) -> A. f e. M ( f supp Z ) C_ ( 0 ... S ) ) )

  proof
    cM
    cR
    cn0
    cmap
    co
    #
    wss
    #
    cM
    cfn
    wcel
    #
    cZ
    cV
    wcel
    #
    w3a
    #
    vf
    cv
    #
    cZ
    cfsupp
    wbr
    #
    vf
    cM
    wral
    #
    cU
    c0
    wne
    #
    wa
    #
    @5
    cZ
    csupp
    co
    #
    cc0
    cS
    cfz
    co
    #
    wss
    #
    vf
    cM
    wral
    @4
    @9
    wa
    #
    @12
    vf
    cM
    @4
    @9
    vf
    @4
    vf
    nfv
    @7
    @8
    vf
    @6
    vf
    cM
    nfra1
    @8
    vf
    nfv
    nfan
    nfan
    #
    @13
    @5
    cM
    wcel
    #
    @12
    @13
    @15
    wa
    #
    vx
    @10
    @11
    @16
    vx
    cv
    #
    @10
    wcel
    #
    @17
    @11
    wcel
    #
    @16
    @18
    wa
    #
    @17
    cn0
    wcel
    #
    cS
    cn0
    wcel
    #
    @17
    cS
    cle
    wbr
    @19
    @16
    @18
    @21
    @4
    @15
    @18
    @21
    wi
    @9
    @4
    @15
    wa
    #
    @10
    cn0
    @17
    @23
    @10
    @5
    cdm
    #
    cn0
    @5
    cZ
    suppssdm
    #
    @1
    @2
    @15
    @24
    cn0
    wss
    #
    @3
    @1
    @15
    wa
    #
    @5
    @0
    wcel
    #
    @5
    cn0
    wfn
    #
    @26
    cM
    @0
    @5
    ssel2
    #
    @5
    cR
    cn0
    elmapfn
    #
    @29
    @24
    cn0
    wceq
    #
    @26
    cn0
    @5
    fndm
    #
    @24
    cn0
    eqimss
    syl
    3syl
    3ad2antl1
    syl5ss
    sseld
    adantlr
    imp
    @13
    @22
    @15
    @18
    @4
    @9
    @22
    cR
    cS
    cU
    vf
    cM
    cV
    cZ
    fsuppmapnn0fiub.u
    fsuppmapnn0fiub.s
    fsuppmapnn0fiublem
    imp
    ad2antrr
    @20
    cU
    @17
    cS
    @20
    cU
    vf
    cM
    @10
    ciun
    #
    cr
    fsuppmapnn0fiub.u
    @20
    @10
    cr
    wss
    #
    vf
    cM
    wral
    #
    @34
    cr
    wss
    @13
    @36
    @15
    @18
    @13
    @35
    vf
    cM
    @14
    @13
    @15
    @35
    @16
    @10
    @24
    cr
    @25
    @16
    @24
    cn0
    cr
    @13
    @15
    @32
    @4
    @15
    @32
    wi
    #
    @9
    @1
    @2
    @37
    @3
    @1
    @15
    @32
    @27
    @28
    @29
    @32
    @30
    @31
    @33
    3syl
    ex
    3ad2ant1
    adantr
    imp
    nn0ssre
    syl6eqss
    syl5ss
    ex
    ralrimi
    ad2antrr
    vf
    cM
    @10
    cr
    iunss
    sylibr
    syl5eqss
    @20
    cU
    @34
    cfn
    fsuppmapnn0fiub.u
    @20
    @2
    @10
    cfn
    wcel
    #
    vf
    cM
    wral
    #
    wa
    #
    @34
    cfn
    wcel
    @13
    @40
    @15
    @18
    @4
    @2
    @9
    @39
    @1
    @2
    @3
    simp2
    @7
    @39
    @8
    @6
    @38
    vf
    cM
    @6
    @5
    cZ
    @6
    id
    fsuppimpd
    ralimi
    adantr
    anim12i
    ad2antrr
    vf
    cM
    @10
    iunfi
    syl
    syl5eqel
    @15
    @18
    @17
    cU
    wcel
    @13
    @15
    @18
    wa
    #
    @17
    @34
    cU
    @41
    @18
    vf
    cM
    wrex
    @17
    @34
    wcel
    @18
    vf
    cM
    rspe
    vf
    @17
    cM
    @10
    eliun
    sylibr
    fsuppmapnn0fiub.u
    syl6eleqr
    adantll
    cS
    cU
    cr
    clt
    csup
    wceq
    @20
    fsuppmapnn0fiub.s
    a1i
    supfirege
    @17
    cS
    elfz2nn0
    syl3anbrc
    ex
    ssrdv
    ex
    ralrimi
    ex
end

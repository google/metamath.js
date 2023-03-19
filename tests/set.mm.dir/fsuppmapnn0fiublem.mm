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
include "ciun.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfan.mm"
include "cdm.mm"
include "suppssdm.mm"
include "wi.mm"
include "wfn.mm"
include "ssel2.mm"
include "elmapfn.mm"
include "wceq.mm"
include "fndm.mm"
include "eqimss.mm"
include "syl.mm"
include "3syl.mm"
include "ex.mm"
include "3ad2ant1.mm"
include "adantr.mm"
include "imp.mm"
include "syl5ss.mm"
include "ralrimi.mm"
include "iunss.mm"
include "sylibr.mm"
include "syl5eqss.mm"
include "cr.mm"
include "clt.mm"
include "wor.mm"
include "ltso.mm"
include "a1i.mm"
include "simp2.mm"
include "id.mm"
include "fsuppimpd.mm"
include "ralimi.mm"
include "iunfi.mm"
include "syl2an.mm"
include "syl5eqel.mm"
include "simprr.mm"
include "nn0ssre.mm"
include "syl6eqss.mm"
include "sseq1i.mm"
include "bitri.mm"
include "csup.mm"
include "fisupcl.mm"
include "syl13anc.mm"
include "sseldd.mm"

theorem fsuppmapnn0fiublem
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
  assert |- ( ( M C_ ( R ^m NN0 ) /\ M e. Fin /\ Z e. V ) -> ( ( A. f e. M f finSupp Z /\ U =/= (/) ) -> S e. NN0 ) )

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
    cS
    cn0
    wcel
    @4
    @9
    wa
    #
    cU
    cn0
    cS
    @10
    cU
    vf
    cM
    @5
    cZ
    csupp
    co
    #
    ciun
    #
    cn0
    fsuppmapnn0fiub.u
    @10
    @11
    cn0
    wss
    #
    vf
    cM
    wral
    @12
    cn0
    wss
    @10
    @13
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
    @10
    @5
    cM
    wcel
    #
    @13
    @10
    @15
    wa
    #
    @11
    @5
    cdm
    #
    cn0
    @5
    cZ
    suppssdm
    #
    @10
    @15
    @17
    cn0
    wss
    #
    @4
    @15
    @19
    wi
    #
    @9
    @1
    @2
    @20
    @3
    @1
    @15
    @19
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
    @19
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
    @23
    @17
    cn0
    wceq
    #
    @19
    cn0
    @5
    fndm
    #
    @17
    cn0
    eqimss
    syl
    3syl
    ex
    3ad2ant1
    adantr
    imp
    syl5ss
    ex
    ralrimi
    vf
    cM
    @11
    cn0
    iunss
    sylibr
    syl5eqss
    @10
    cr
    clt
    wor
    #
    cU
    cfn
    wcel
    #
    @8
    cU
    cr
    wss
    #
    cS
    cU
    wcel
    @28
    @10
    ltso
    a1i
    @10
    cU
    @12
    cfn
    fsuppmapnn0fiub.u
    @4
    @2
    @11
    cfn
    wcel
    #
    vf
    cM
    wral
    #
    @12
    cfn
    wcel
    @9
    @1
    @2
    @3
    simp2
    @7
    @32
    @8
    @6
    @31
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
    vf
    cM
    @11
    iunfi
    syl2an
    syl5eqel
    @4
    @7
    @8
    simprr
    @10
    @11
    cr
    wss
    #
    vf
    cM
    wral
    #
    @30
    @10
    @33
    vf
    cM
    @14
    @10
    @15
    @33
    @16
    @11
    @17
    cr
    @18
    @16
    @17
    cn0
    cr
    @10
    @15
    @26
    @4
    @15
    @26
    wi
    #
    @9
    @1
    @2
    @35
    @3
    @1
    @15
    @26
    @21
    @22
    @23
    @26
    @24
    @25
    @27
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
    @30
    @12
    cr
    wss
    @34
    cU
    @12
    cr
    fsuppmapnn0fiub.u
    sseq1i
    vf
    cM
    @11
    cr
    iunss
    bitri
    sylibr
    @28
    @29
    @8
    @30
    w3a
    wa
    cS
    cU
    cr
    clt
    csup
    cU
    fsuppmapnn0fiub.s
    cr
    cU
    clt
    fisupcl
    syl5eqel
    syl13anc
    sseldd
    ex
end

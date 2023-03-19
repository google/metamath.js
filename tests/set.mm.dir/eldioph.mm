include "cn0.mm"
include "wcel.mm"
include "cuz.mm"
include "cfv.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cmzp.mm"
include "w3a.mm"
include "cv.mm"
include "cres.mm"
include "wceq.mm"
include "cc0.mm"
include "wa.mm"
include "cmap.mm"
include "wrex.mm"
include "cab.mm"
include "cdioph.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "eqidd.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "abbidv.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "rexeqdv.mm"
include "rexeqbidv.mm"
include "eldiophb.mm"
include "sylanbrc.mm"

theorem eldioph
  let vu: setvar u
  let vt: setvar t
  let cP: class P
  let cK: class K
  let cN: class N
  let vk: setvar k
  let vp: setvar p

  disjoint N t
  disjoint N u
  disjoint t u
  disjoint K t
  disjoint K u
  disjoint P t
  disjoint P u
  disjoint N k
  disjoint N p
  disjoint k p
  disjoint k t
  disjoint k u
  disjoint p t
  disjoint p u
  disjoint K k
  disjoint K p
  disjoint P k
  disjoint P p
  assert |- ( ( N e. NN0 /\ K e. ( ZZ>= ` N ) /\ P e. ( mzPoly ` ( 1 ... K ) ) ) -> { t | E. u e. ( NN0 ^m ( 1 ... K ) ) ( t = ( u |` ( 1 ... N ) ) /\ ( P ` u ) = 0 ) } e. ( Dioph ` N ) )

  proof
    cN
    cn0
    wcel
    #
    cK
    cN
    cuz
    cfv
    #
    wcel
    #
    cP
    c1
    cK
    cfz
    co
    #
    cmzp
    cfv
    #
    wcel
    #
    w3a
    #
    @0
    vt
    cv
    vu
    cv
    #
    c1
    cN
    cfz
    co
    cres
    wceq
    #
    @7
    cP
    cfv
    #
    cc0
    wceq
    #
    wa
    #
    vu
    cn0
    @3
    cmap
    co
    #
    wrex
    #
    vt
    cab
    #
    @8
    @7
    vp
    cv
    #
    cfv
    #
    cc0
    wceq
    #
    wa
    #
    vu
    cn0
    c1
    vk
    cv
    #
    cfz
    co
    #
    cmap
    co
    #
    wrex
    #
    vt
    cab
    #
    wceq
    #
    vp
    @20
    cmzp
    cfv
    #
    wrex
    #
    vk
    @1
    wrex
    #
    @14
    cN
    cdioph
    cfv
    wcel
    @0
    @2
    @5
    simp1
    @6
    @2
    @14
    @18
    vu
    @12
    wrex
    #
    vt
    cab
    #
    wceq
    #
    vp
    @4
    wrex
    #
    @27
    @0
    @2
    @5
    simp2
    @6
    @5
    @14
    @14
    wceq
    #
    @31
    @0
    @2
    @5
    simp3
    @6
    @14
    eqidd
    @30
    @32
    vp
    cP
    @4
    @15
    cP
    wceq
    #
    @29
    @14
    @14
    @33
    @28
    @13
    vt
    @33
    @18
    @11
    vu
    @12
    @33
    @17
    @10
    @8
    @33
    @16
    @9
    cc0
    @7
    @15
    cP
    fveq1
    eqeq1d
    anbi2d
    rexbidv
    abbidv
    eqeq2d
    rspcev
    syl2anc
    @26
    @31
    vk
    cK
    @1
    @19
    cK
    wceq
    #
    @24
    @30
    vp
    @25
    @4
    @34
    @20
    @3
    cmzp
    @19
    cK
    c1
    cfz
    oveq2
    #
    fveq2d
    @34
    @23
    @29
    @14
    @34
    @22
    @28
    vt
    @34
    @18
    vu
    @21
    @12
    @34
    @20
    @3
    cn0
    cmap
    @35
    oveq2d
    rexeqdv
    abbidv
    eqeq2d
    rexeqbidv
    rspcev
    syl2anc
    vu
    vt
    @14
    vk
    cN
    vp
    eldiophb
    sylanbrc
end

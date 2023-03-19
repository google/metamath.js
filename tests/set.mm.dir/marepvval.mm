include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cfv.mm"
include "weq.mm"
include "cv.mm"
include "cif.mm"
include "cmpt2.mm"
include "cmpt.mm"
include "wceq.mm"
include "marepvval0.mm"
include "3adant3.mm"
include "fveq1d.mm"
include "cvv.mm"
include "simp3.mm"
include "cfn.mm"
include "wa.mm"
include "matrcl.mm"
include "simpld.mm"
include "jca.mm"
include "3ad2ant1.mm"
include "mpt2exga.mm"
include "syl.mm"
include "eqeq2.mm"
include "ifbid.mm"
include "mpt2eq3dv.mm"
include "eqid.mm"
include "fvmptg.mm"
include "syl2anc.mm"
include "eqtrd.mm"

theorem marepvval
  let cA: class A
  let cB: class B
  let cC: class C
  let cQ: class Q
  let cR: class R
  let vi: setvar i
  let vj: setvar j
  let cK: class K
  let cM: class M
  let cN: class N
  let cV: class V
  let vm: setvar m
  let vn: setvar n
  let vr: setvar r
  let vv: setvar v
  let vk: setvar k
  let vc: setvar c
  assume marepvfval.a: |- A = ( N Mat R )
  assume marepvfval.b: |- B = ( Base ` A )
  assume marepvfval.q: |- Q = ( N matRepV R )
  assume marepvfval.v: |- V = ( ( Base ` R ) ^m N )

  disjoint N i
  disjoint N j
  disjoint i j
  disjoint R i
  disjoint R j
  disjoint C i
  disjoint C j
  disjoint M i
  disjoint M j
  disjoint K i
  disjoint K j
  disjoint B m
  disjoint B n
  disjoint B r
  disjoint B v
  disjoint m n
  disjoint m r
  disjoint m v
  disjoint n r
  disjoint n v
  disjoint r v
  disjoint N k
  disjoint N m
  disjoint N n
  disjoint N r
  disjoint N v
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i r
  disjoint i v
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j r
  disjoint j v
  disjoint k m
  disjoint k n
  disjoint k r
  disjoint k v
  disjoint R k
  disjoint R m
  disjoint R n
  disjoint R r
  disjoint R v
  disjoint V m
  disjoint V n
  disjoint V r
  disjoint V v
  disjoint B c
  disjoint C c
  disjoint C k
  disjoint C m
  disjoint c i
  disjoint c j
  disjoint c k
  disjoint c m
  disjoint M c
  disjoint M k
  disjoint M m
  disjoint N c
  disjoint R c
  disjoint V c
  disjoint K k
  assert |- ( ( M e. B /\ C e. V /\ K e. N ) -> ( ( M Q C ) ` K ) = ( i e. N , j e. N |-> if ( j = K , ( C ` i ) , ( i M j ) ) ) )

  proof
    cM
    cB
    wcel
    #
    cC
    cV
    wcel
    #
    cK
    cN
    wcel
    #
    w3a
    #
    cK
    cM
    cC
    cQ
    co
    #
    cfv
    cK
    vk
    cN
    vi
    vj
    cN
    cN
    vj
    vk
    weq
    #
    vi
    cv
    #
    cC
    cfv
    #
    @6
    vj
    cv
    #
    cM
    co
    #
    cif
    #
    cmpt2
    #
    cmpt
    #
    cfv
    #
    vi
    vj
    cN
    cN
    @8
    cK
    wceq
    #
    @7
    @9
    cif
    #
    cmpt2
    #
    @3
    cK
    @4
    @12
    @0
    @1
    @4
    @12
    wceq
    @2
    cA
    cB
    cC
    cQ
    cR
    vi
    vj
    vk
    cM
    cN
    cV
    marepvfval.a
    marepvfval.b
    marepvfval.q
    marepvfval.v
    marepvval0
    3adant3
    fveq1d
    @3
    @2
    @16
    cvv
    wcel
    #
    @13
    @16
    wceq
    @0
    @1
    @2
    simp3
    @3
    cN
    cfn
    wcel
    #
    @18
    wa
    #
    @17
    @0
    @1
    @19
    @2
    @0
    @18
    @18
    @0
    @18
    cR
    cvv
    wcel
    cA
    cB
    cR
    cN
    cM
    marepvfval.a
    marepvfval.b
    matrcl
    simpld
    #
    @20
    jca
    3ad2ant1
    vi
    vj
    cN
    cN
    @15
    cfn
    cfn
    mpt2exga
    syl
    vk
    cK
    @11
    @16
    cN
    cvv
    @12
    vk
    cv
    #
    cK
    wceq
    #
    vi
    vj
    cN
    cN
    @10
    @15
    @22
    @5
    @14
    @7
    @9
    @21
    cK
    @8
    eqeq2
    ifbid
    mpt2eq3dv
    @12
    eqid
    fvmptg
    syl2anc
    eqtrd
end

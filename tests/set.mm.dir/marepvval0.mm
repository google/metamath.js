include "wcel.mm"
include "weq.mm"
include "cv.mm"
include "cfv.mm"
include "co.mm"
include "cif.mm"
include "cmpt2.mm"
include "cmpt.mm"
include "cvv.mm"
include "wceq.mm"
include "wa.mm"
include "cfn.mm"
include "matrcl.mm"
include "simpld.mm"
include "adantr.mm"
include "mptexg.mm"
include "syl.mm"
include "fveq1.mm"
include "adantl.mm"
include "oveq.mm"
include "ifeq12d.mm"
include "mpt2eq3dv.mm"
include "mpteq2dv.mm"
include "marepvfval.mm"
include "ovmpt2ga.mm"
include "mpd3an3.mm"

theorem marepvval0
  let cA: class A
  let cB: class B
  let cC: class C
  let cQ: class Q
  let cR: class R
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let cM: class M
  let cN: class N
  let cV: class V
  let vm: setvar m
  let vn: setvar n
  let vr: setvar r
  let vv: setvar v
  let vc: setvar c
  assume marepvfval.a: |- A = ( N Mat R )
  assume marepvfval.b: |- B = ( Base ` A )
  assume marepvfval.q: |- Q = ( N matRepV R )
  assume marepvfval.v: |- V = ( ( Base ` R ) ^m N )

  disjoint N i
  disjoint N j
  disjoint N k
  disjoint i j
  disjoint i k
  disjoint j k
  disjoint R i
  disjoint R j
  disjoint R k
  disjoint C i
  disjoint C j
  disjoint C k
  disjoint M i
  disjoint M j
  disjoint M k
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
  disjoint N m
  disjoint N n
  disjoint N r
  disjoint N v
  disjoint i m
  disjoint i n
  disjoint i r
  disjoint i v
  disjoint j m
  disjoint j n
  disjoint j r
  disjoint j v
  disjoint k m
  disjoint k n
  disjoint k r
  disjoint k v
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
  disjoint C m
  disjoint c i
  disjoint c j
  disjoint c k
  disjoint c m
  disjoint M c
  disjoint M m
  disjoint N c
  disjoint R c
  disjoint V c
  assert |- ( ( M e. B /\ C e. V ) -> ( M Q C ) = ( k e. N |-> ( i e. N , j e. N |-> if ( j = k , ( C ` i ) , ( i M j ) ) ) ) )

  proof
    cM
    cB
    wcel
    #
    cC
    cV
    wcel
    #
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
    @3
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
    cvv
    wcel
    #
    cM
    cC
    cQ
    co
    @9
    wceq
    @0
    @1
    wa
    cN
    cfn
    wcel
    #
    @10
    @0
    @11
    @1
    @0
    @11
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
    adantr
    vk
    cN
    @8
    cfn
    mptexg
    syl
    vm
    vc
    cM
    cC
    cB
    cV
    vk
    cN
    vi
    vj
    cN
    cN
    @2
    @3
    vc
    cv
    #
    cfv
    #
    @3
    @5
    vm
    cv
    #
    co
    #
    cif
    #
    cmpt2
    #
    cmpt
    @9
    cQ
    cvv
    @14
    cM
    wceq
    #
    @12
    cC
    wceq
    #
    wa
    #
    vk
    cN
    @17
    @8
    @20
    vi
    vj
    cN
    cN
    @16
    @7
    @20
    @2
    @13
    @4
    @15
    @6
    @19
    @13
    @4
    wceq
    @18
    @3
    @12
    cC
    fveq1
    adantl
    @18
    @15
    @6
    wceq
    @19
    @3
    @5
    @14
    cM
    oveq
    adantr
    ifeq12d
    mpt2eq3dv
    mpteq2dv
    vc
    cA
    cB
    cQ
    cR
    vi
    vj
    vk
    vm
    cN
    cV
    marepvfval.a
    marepvfval.b
    marepvfval.q
    marepvfval.v
    marepvfval
    ovmpt2ga
    mpd3an3
end

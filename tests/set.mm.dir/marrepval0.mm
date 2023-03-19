include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "weq.mm"
include "cif.mm"
include "cv.mm"
include "co.mm"
include "cmpt2.mm"
include "cvv.mm"
include "wceq.mm"
include "wa.mm"
include "cfn.mm"
include "matrcl.mm"
include "simpld.mm"
include "jca.mm"
include "adantr.mm"
include "mpt2exga.mm"
include "syl.mm"
include "ifeq1.mm"
include "adantl.mm"
include "oveq.mm"
include "ifeq12d.mm"
include "mpt2eq3dv.mm"
include "marrepfval.mm"
include "ovmpt2ga.mm"
include "mpd3an3.mm"

theorem marrepval0
  let cA: class A
  let cB: class B
  let cQ: class Q
  let cR: class R
  let cS: class S
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let cM: class M
  let cN: class N
  let c.0: class .0.
  let vl: setvar l
  let vm: setvar m
  let vn: setvar n
  let vr: setvar r
  let vs: setvar s
  assume marrepfval.a: |- A = ( N Mat R )
  assume marrepfval.b: |- B = ( Base ` A )
  assume marrepfval.q: |- Q = ( N matRRep R )
  assume marrepfval.z: |- .0. = ( 0g ` R )

  disjoint N i
  disjoint N j
  disjoint N k
  disjoint N l
  disjoint i j
  disjoint i k
  disjoint i l
  disjoint j k
  disjoint j l
  disjoint k l
  disjoint R i
  disjoint R j
  disjoint R k
  disjoint R l
  disjoint M i
  disjoint M j
  disjoint M k
  disjoint M l
  disjoint S i
  disjoint S j
  disjoint S k
  disjoint S l
  disjoint B m
  disjoint B n
  disjoint B r
  disjoint B s
  disjoint m n
  disjoint m r
  disjoint m s
  disjoint n r
  disjoint n s
  disjoint r s
  disjoint N m
  disjoint N n
  disjoint N r
  disjoint N s
  disjoint i m
  disjoint i n
  disjoint i r
  disjoint i s
  disjoint j m
  disjoint j n
  disjoint j r
  disjoint j s
  disjoint k m
  disjoint k n
  disjoint k r
  disjoint k s
  disjoint l m
  disjoint l n
  disjoint l r
  disjoint l s
  disjoint R m
  disjoint R n
  disjoint R r
  disjoint R s
  disjoint .0. n
  disjoint .0. r
  disjoint M m
  disjoint M s
  disjoint S m
  disjoint S s
  disjoint .0. m
  disjoint .0. s
  assert |- ( ( M e. B /\ S e. ( Base ` R ) ) -> ( M Q S ) = ( k e. N , l e. N |-> ( i e. N , j e. N |-> if ( i = k , if ( j = l , S , .0. ) , ( i M j ) ) ) ) )

  proof
    cM
    cB
    wcel
    #
    cS
    cR
    cbs
    cfv
    #
    wcel
    #
    vk
    vl
    cN
    cN
    vi
    vj
    cN
    cN
    vi
    vk
    weq
    #
    vj
    vl
    weq
    #
    cS
    c.0
    cif
    #
    vi
    cv
    #
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
    cmpt2
    #
    cvv
    wcel
    #
    cM
    cS
    cQ
    co
    @11
    wceq
    @0
    @2
    wa
    cN
    cfn
    wcel
    #
    @13
    wa
    #
    @12
    @0
    @14
    @2
    @0
    @13
    @13
    @0
    @13
    cR
    cvv
    wcel
    cA
    cB
    cR
    cN
    cM
    marrepfval.a
    marrepfval.b
    matrcl
    simpld
    #
    @15
    jca
    adantr
    vk
    vl
    cN
    cN
    @10
    cfn
    cfn
    mpt2exga
    syl
    vm
    vs
    cM
    cS
    cB
    @1
    vk
    vl
    cN
    cN
    vi
    vj
    cN
    cN
    @3
    @4
    vs
    cv
    #
    c.0
    cif
    #
    @6
    @7
    vm
    cv
    #
    co
    #
    cif
    #
    cmpt2
    #
    cmpt2
    @11
    cQ
    cvv
    @18
    cM
    wceq
    #
    @16
    cS
    wceq
    #
    wa
    #
    vk
    vl
    cN
    cN
    @21
    @10
    @24
    vi
    vj
    cN
    cN
    @20
    @9
    @24
    @3
    @17
    @5
    @19
    @8
    @23
    @17
    @5
    wceq
    @22
    @4
    @16
    cS
    c.0
    ifeq1
    adantl
    @22
    @19
    @8
    wceq
    @23
    @6
    @7
    @18
    cM
    oveq
    adantr
    ifeq12d
    mpt2eq3dv
    mpt2eq3dv
    cA
    cB
    cQ
    cR
    vi
    vj
    vk
    vm
    cN
    c.0
    vs
    vl
    marrepfval.a
    marrepfval.b
    marrepfval.q
    marrepfval.z
    marrepfval
    ovmpt2ga
    mpd3an3
end

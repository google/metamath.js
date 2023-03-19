include "cn.mm"
include "wcel.mm"
include "cz.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cv.mm"
include "cneg.mm"
include "cexp.mm"
include "cmul.mm"
include "cfl.mm"
include "cfv.mm"
include "cmo.mm"
include "cmpt2.mm"
include "cdig.mm"
include "cvv.mm"
include "cmpt.mm"
include "wceq.mm"
include "df-dig.mm"
include "a1i.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "id.mm"
include "oveq12d.mm"
include "mpt2eq3dv.mm"
include "adantl.mm"
include "wa.mm"
include "zex.mm"
include "ovex.mm"
include "pm3.2i.mm"
include "eqid.mm"
include "mpt2exg.mm"
include "mp1i.mm"
include "fvmptd.mm"

theorem digfval
  let cB: class B
  let vk: setvar k
  let vr: setvar r
  let vb: setvar b
  let vx: setvar x

  disjoint k r
  disjoint B k
  disjoint B r
  disjoint b k
  disjoint b r
  disjoint B b
  disjoint k x
  assert |- ( B e. NN -> ( digit ` B ) = ( k e. ZZ , r e. ( 0 [,) +oo ) |-> ( ( |_ ` ( ( B ^ -u k ) x. r ) ) mod B ) ) )

  proof
    cB
    cn
    wcel
    #
    vb
    cB
    vk
    vr
    cz
    cc0
    cpnf
    cico
    co
    #
    vb
    cv
    #
    vk
    cv
    cneg
    #
    cexp
    co
    #
    vr
    cv
    #
    cmul
    co
    #
    cfl
    cfv
    #
    @2
    cmo
    co
    #
    cmpt2
    #
    vk
    vr
    cz
    @1
    cB
    @3
    cexp
    co
    #
    @5
    cmul
    co
    #
    cfl
    cfv
    #
    cB
    cmo
    co
    #
    cmpt2
    #
    cn
    cdig
    cvv
    cdig
    vb
    cn
    @9
    cmpt
    wceq
    @0
    vk
    vr
    vb
    df-dig
    a1i
    @2
    cB
    wceq
    #
    @9
    @14
    wceq
    @0
    @15
    vk
    vr
    cz
    @1
    @8
    @13
    @15
    @7
    @12
    @2
    cB
    cmo
    @15
    @6
    @11
    cfl
    @15
    @4
    @10
    @5
    cmul
    @2
    cB
    @3
    cexp
    oveq1
    oveq1d
    fveq2d
    @15
    id
    oveq12d
    mpt2eq3dv
    adantl
    @0
    id
    cz
    cvv
    wcel
    #
    @1
    cvv
    wcel
    #
    wa
    @14
    cvv
    wcel
    @0
    @16
    @17
    zex
    cc0
    cpnf
    cico
    ovex
    pm3.2i
    vk
    vr
    cz
    @1
    @13
    cvv
    cvv
    @14
    @14
    eqid
    mpt2exg
    mp1i
    fvmptd
end

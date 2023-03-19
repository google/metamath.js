include "c0.mm"
include "cc0.mm"
include "cfv.mm"
include "wcel.mm"
include "wn.mm"
include "noel.mm"
include "c2o.mm"
include "cn0.mm"
include "cv.mm"
include "wcad.mm"
include "c1o.mm"
include "cif.mm"
include "cmpt2.mm"
include "wceq.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cmpt.mm"
include "cseq.mm"
include "fveq1i.mm"
include "cz.mm"
include "0z.mm"
include "seq1.mm"
include "ax-mp.mm"
include "0nn0.mm"
include "iftrue.mm"
include "eqid.mm"
include "0ex.mm"
include "fvmpt.mm"
include "3eqtri.mm"
include "eleq2i.mm"
include "mtbir.mm"
include "a1i.mm"

theorem sadc0
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vm: setvar m
  let vn: setvar n
  let vc: setvar c
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  let cN: class N
  let cK: class K
  assume sadval.a: |- ( ph -> A C_ NN0 )
  assume sadval.b: |- ( ph -> B C_ NN0 )
  assume sadval.c: |- C = seq 0 ( ( c e. 2o , m e. NN0 |-> if ( cadd ( m e. A , m e. B , (/) e. c ) , 1o , (/) ) ) , ( n e. NN0 |-> if ( n = 0 , (/) , ( n - 1 ) ) ) )

  disjoint c m
  disjoint c n
  disjoint m n
  disjoint A c
  disjoint A m
  disjoint B c
  disjoint B m
  disjoint c k
  disjoint c x
  disjoint c y
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint m x
  disjoint m y
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint A k
  disjoint A x
  disjoint A y
  disjoint B k
  disjoint B x
  disjoint B y
  disjoint N k
  disjoint N n
  disjoint N x
  disjoint N y
  disjoint C k
  disjoint C x
  disjoint C y
  disjoint K k
  disjoint K x
  disjoint k ph
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> -. (/) e. ( C ` 0 ) )

  proof
    c0
    cc0
    cC
    cfv
    #
    wcel
    #
    wn
    wph
    @1
    c0
    c0
    wcel
    c0
    noel
    @0
    c0
    c0
    @0
    cc0
    vc
    vm
    c2o
    cn0
    vm
    cv
    #
    cA
    wcel
    @2
    cB
    wcel
    c0
    vc
    cv
    wcel
    wcad
    c1o
    c0
    cif
    cmpt2
    #
    vn
    cn0
    vn
    cv
    #
    cc0
    wceq
    #
    c0
    @4
    c1
    cmin
    co
    #
    cif
    #
    cmpt
    #
    cc0
    cseq
    #
    cfv
    #
    cc0
    @8
    cfv
    #
    c0
    cc0
    cC
    @9
    sadval.c
    fveq1i
    cc0
    cz
    wcel
    @10
    @11
    wceq
    0z
    @3
    @8
    cc0
    seq1
    ax-mp
    cc0
    cn0
    wcel
    @11
    c0
    wceq
    0nn0
    vn
    cc0
    @7
    c0
    cn0
    @8
    @5
    c0
    @6
    iftrue
    @8
    eqid
    0ex
    fvmpt
    ax-mp
    3eqtri
    eleq2i
    mtbir
    a1i
end

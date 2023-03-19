include "cmin.mm"
include "co.mm"
include "cdiv.mm"
include "ccj.mm"
include "cfv.mm"
include "cr.mm"
include "cc.mm"
include "wcel.mm"
include "simp2d.mm"
include "simp1d.mm"
include "subcld.mm"
include "simp3d.mm"
include "neqned.mm"
include "subne0d.mm"
include "cjdivd.mm"
include "cmul.mm"
include "cjcld.mm"
include "cjne0d.mm"
include "divcan5rd.mm"
include "mulcld.mm"
include "cim.mm"
include "cc0.mm"
include "wceq.mm"
include "sigarval.mm"
include "syl2anc.mm"
include "eqtr3d.mm"
include "reim0bd.mm"
include "mulcomd.mm"
include "cjmulrcld.mm"
include "eqeltrrd.mm"
include "mulne0d.mm"
include "redivcld.mm"
include "eqeltrd.mm"
include "cjred.mm"
include "divcld.mm"
include "cjcjd.mm"

theorem sigardiv
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cG: class G
  let vk: setvar k
  assume sigar: |- G = ( x e. CC , y e. CC |-> ( Im ` ( ( * ` x ) x. y ) ) )
  assume sigardiv.a: |- ( ph -> ( A e. CC /\ B e. CC /\ C e. CC ) )
  assume sigardiv.b: |- ( ph -> -. C = A )
  assume sigardiv.c: |- ( ph -> ( ( B - A ) G ( C - A ) ) = 0 )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint k x
  assert |- ( ph -> ( ( B - A ) / ( C - A ) ) e. RR )

  proof
    wph
    cB
    cA
    cmin
    co
    #
    cC
    cA
    cmin
    co
    #
    cdiv
    co
    #
    ccj
    cfv
    #
    @2
    cr
    wph
    @3
    ccj
    cfv
    @3
    @2
    wph
    @3
    wph
    @3
    @0
    ccj
    cfv
    #
    @1
    ccj
    cfv
    #
    cdiv
    co
    #
    cr
    wph
    @0
    @1
    wph
    cB
    cA
    wph
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    cC
    cc
    wcel
    #
    sigardiv.a
    simp2d
    wph
    @7
    @8
    @9
    sigardiv.a
    simp1d
    #
    subcld
    #
    wph
    cC
    cA
    wph
    @7
    @8
    @9
    sigardiv.a
    simp3d
    #
    @10
    subcld
    #
    wph
    cC
    cA
    @12
    @10
    wph
    cC
    cA
    sigardiv.b
    neqned
    subne0d
    #
    cjdivd
    wph
    @4
    @1
    cmul
    co
    #
    @5
    @1
    cmul
    co
    #
    cdiv
    co
    @6
    cr
    wph
    @4
    @5
    @1
    wph
    @0
    @11
    cjcld
    #
    wph
    @1
    @13
    cjcld
    #
    @13
    wph
    @1
    @13
    @14
    cjne0d
    #
    @14
    divcan5rd
    wph
    @15
    @16
    wph
    @15
    wph
    @4
    @1
    @17
    @13
    mulcld
    wph
    @0
    @1
    cG
    co
    #
    @15
    cim
    cfv
    #
    cc0
    wph
    @0
    cc
    wcel
    @1
    cc
    wcel
    @20
    @21
    wceq
    @11
    @13
    vx
    vy
    @0
    @1
    cG
    sigar
    sigarval
    syl2anc
    sigardiv.c
    eqtr3d
    reim0bd
    wph
    @1
    @5
    cmul
    co
    @16
    cr
    wph
    @1
    @5
    @13
    @18
    mulcomd
    wph
    @1
    @13
    cjmulrcld
    eqeltrrd
    wph
    @5
    @1
    @18
    @13
    @19
    @14
    mulne0d
    redivcld
    eqeltrrd
    eqeltrd
    #
    cjred
    wph
    @2
    wph
    @0
    @1
    @11
    @13
    @14
    divcld
    cjcjd
    eqtr3d
    @22
    eqeltrrd
end

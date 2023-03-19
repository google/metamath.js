include "cv.mm"
include "cxr.mm"
include "wcel.mm"
include "cr.mm"
include "cpnf.mm"
include "wceq.mm"
include "cmnf.mm"
include "w3o.mm"
include "ccnv.mm"
include "cioo.mm"
include "co.mm"
include "cima.mm"
include "cvol.mm"
include "cdm.mm"
include "elxr.mm"
include "c0.mm"
include "oveq1.mm"
include "iooid.mm"
include "syl6eq.mm"
include "imaeq2d.mm"
include "ima0.mm"
include "0mbl.mm"
include "eqeltri.mm"
include "syl6eqel.mm"
include "adantl.mm"
include "wf.mm"
include "fimacnv.mm"
include "syl.mm"
include "eqeltrd.mm"
include "ioomax.mm"
include "eleq1d.mm"
include "syl5ibrcom.mm"
include "imp.mm"
include "3jaodan.mm"
include "sylan2b.mm"
include "oveq2.mm"
include "ismbfd.mm"

theorem ismbf2d
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cF: class F
  assume ismbf2d.1: |- ( ph -> F : A --> RR )
  assume ismbf2d.2: |- ( ph -> A e. dom vol )
  assume ismbf2d.3: |- ( ( ph /\ x e. RR ) -> ( `' F " ( x (,) +oo ) ) e. dom vol )
  assume ismbf2d.4: |- ( ( ph /\ x e. RR ) -> ( `' F " ( -oo (,) x ) ) e. dom vol )

  disjoint F x
  disjoint ph x
  assert |- ( ph -> F e. MblFn )

  proof
    wph
    vx
    cA
    cF
    ismbf2d.1
    vx
    cv
    #
    cxr
    wcel
    #
    wph
    @0
    cr
    wcel
    #
    @0
    cpnf
    wceq
    #
    @0
    cmnf
    wceq
    #
    w3o
    #
    cF
    ccnv
    #
    @0
    cpnf
    cioo
    co
    #
    cima
    #
    cvol
    cdm
    #
    wcel
    #
    @0
    elxr
    #
    wph
    @2
    @10
    @3
    @4
    ismbf2d.3
    @3
    @10
    wph
    @3
    @8
    @6
    c0
    cima
    #
    @9
    @3
    @7
    c0
    @6
    @3
    @7
    cpnf
    cpnf
    cioo
    co
    c0
    @0
    cpnf
    cpnf
    cioo
    oveq1
    cpnf
    iooid
    syl6eq
    imaeq2d
    @12
    c0
    @9
    @6
    ima0
    0mbl
    eqeltri
    #
    syl6eqel
    adantl
    wph
    @4
    @10
    wph
    @10
    @4
    @6
    cr
    cima
    #
    @9
    wcel
    #
    wph
    @14
    cA
    @9
    wph
    cA
    cr
    cF
    wf
    @14
    cA
    wceq
    ismbf2d.1
    cA
    cr
    cF
    fimacnv
    syl
    ismbf2d.2
    eqeltrd
    #
    @4
    @8
    @14
    @9
    @4
    @7
    cr
    @6
    @4
    @7
    cmnf
    cpnf
    cioo
    co
    #
    cr
    @0
    cmnf
    cpnf
    cioo
    oveq1
    ioomax
    syl6eq
    imaeq2d
    eleq1d
    syl5ibrcom
    imp
    3jaodan
    sylan2b
    @1
    wph
    @5
    @6
    cmnf
    @0
    cioo
    co
    #
    cima
    #
    @9
    wcel
    #
    @11
    wph
    @2
    @20
    @3
    @4
    ismbf2d.4
    wph
    @3
    @20
    wph
    @20
    @3
    @15
    @16
    @3
    @19
    @14
    @9
    @3
    @18
    cr
    @6
    @3
    @18
    @17
    cr
    @0
    cpnf
    cmnf
    cioo
    oveq2
    ioomax
    syl6eq
    imaeq2d
    eleq1d
    syl5ibrcom
    imp
    @4
    @20
    wph
    @4
    @19
    @12
    @9
    @4
    @18
    c0
    @6
    @4
    @18
    cmnf
    cmnf
    cioo
    co
    c0
    @0
    cmnf
    cmnf
    cioo
    oveq2
    cmnf
    iooid
    syl6eq
    imaeq2d
    @13
    syl6eqel
    adantl
    3jaodan
    sylan2b
    ismbfd
end

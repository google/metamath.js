include "cfv.mm"
include "cpw.mm"
include "cmap.mm"
include "co.mm"
include "cv.mm"
include "cdif.mm"
include "cmpt.mm"
include "cvv.mm"
include "wceq.mm"
include "a1i.mm"
include "pweq.mm"
include "oveq12d.mm"
include "id.mm"
include "difeq1.mm"
include "fveq2d.mm"
include "difeq12d.mm"
include "mpteq12dv.mm"
include "adantl.mm"
include "elexd.mm"
include "wcel.mm"
include "ovex.mm"
include "mptexg.mm"
include "mp1i.mm"
include "fvmptd.mm"
include "syl5eq.mm"

theorem dssmapfvd
  let wph: wff ph
  let cB: class B
  let cD: class D
  let vf: setvar f
  let cO: class O
  let cV: class V
  let vs: setvar s
  let vb: setvar b
  assume dssmapfvd.o: |- O = ( b e. _V |-> ( f e. ( ~P b ^m ~P b ) |-> ( s e. ~P b |-> ( b \ ( f ` ( b \ s ) ) ) ) ) )
  assume dssmapfvd.d: |- D = ( O ` B )
  assume dssmapfvd.b: |- ( ph -> B e. V )

  disjoint B b
  disjoint B f
  disjoint b f
  disjoint B s
  disjoint b s
  disjoint b ph
  assert |- ( ph -> D = ( f e. ( ~P B ^m ~P B ) |-> ( s e. ~P B |-> ( B \ ( f ` ( B \ s ) ) ) ) ) )

  proof
    wph
    cD
    cB
    cO
    cfv
    vf
    cB
    cpw
    #
    @0
    cmap
    co
    #
    vs
    @0
    cB
    cB
    vs
    cv
    #
    cdif
    #
    vf
    cv
    #
    cfv
    #
    cdif
    #
    cmpt
    #
    cmpt
    #
    dssmapfvd.d
    wph
    vb
    cB
    vf
    vb
    cv
    #
    cpw
    #
    @10
    cmap
    co
    #
    vs
    @10
    @9
    @9
    @2
    cdif
    #
    @4
    cfv
    #
    cdif
    #
    cmpt
    #
    cmpt
    #
    @8
    cvv
    cO
    cvv
    cO
    vb
    cvv
    @16
    cmpt
    wceq
    wph
    dssmapfvd.o
    a1i
    @9
    cB
    wceq
    #
    @16
    @8
    wceq
    wph
    @17
    vf
    @11
    @15
    @1
    @7
    @17
    @10
    @0
    @10
    @0
    cmap
    @9
    cB
    pweq
    #
    @18
    oveq12d
    @17
    vs
    @10
    @14
    @0
    @6
    @18
    @17
    @9
    cB
    @13
    @5
    @17
    id
    @17
    @12
    @3
    @4
    @9
    cB
    @2
    difeq1
    fveq2d
    difeq12d
    mpteq12dv
    mpteq12dv
    adantl
    wph
    cB
    cV
    dssmapfvd.b
    elexd
    @1
    cvv
    wcel
    @8
    cvv
    wcel
    wph
    @0
    @0
    cmap
    ovex
    vf
    @1
    @7
    cvv
    mptexg
    mp1i
    fvmptd
    syl5eq
end

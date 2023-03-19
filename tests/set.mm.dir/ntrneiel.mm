include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "cpw.mm"
include "crab.mm"
include "wb.mm"
include "wceq.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "elrab3.mm"
include "syl.mm"
include "cvv.mm"
include "ntrneibex.mm"
include "pwexg.mm"
include "ntrneiiex.mm"
include "eqid.mm"
include "fsovfvfvd.mm"
include "ntrneifv1.mm"
include "fveq1d.mm"
include "eqtr3d.mm"
include "bitr3d.mm"

theorem ntrneiel
  let wph: wff ph
  let cB: class B
  let cS: class S
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let cF: class F
  let cI: class I
  let cN: class N
  let cO: class O
  let cX: class X
  let vl: setvar l
  assume ntrnei.o: |- O = ( i e. _V , j e. _V |-> ( k e. ( ~P j ^m i ) |-> ( l e. j |-> { m e. i | l e. ( k ` m ) } ) ) )
  assume ntrnei.f: |- F = ( ~P B O B )
  assume ntrnei.r: |- ( ph -> I F N )
  assume ntrnei.x: |- ( ph -> X e. B )
  assume ntrnei.s: |- ( ph -> S e. ~P B )

  disjoint B i
  disjoint B j
  disjoint B k
  disjoint B l
  disjoint B m
  disjoint i j
  disjoint i k
  disjoint i l
  disjoint i m
  disjoint j k
  disjoint j l
  disjoint j m
  disjoint k l
  disjoint k m
  disjoint l m
  disjoint I k
  disjoint I l
  disjoint I m
  disjoint S m
  disjoint X l
  disjoint X m
  disjoint i ph
  disjoint j ph
  disjoint k ph
  disjoint l ph
  assert |- ( ph -> ( X e. ( I ` S ) <-> S e. ( N ` X ) ) )

  proof
    wph
    cS
    cX
    vm
    cv
    #
    cI
    cfv
    #
    wcel
    #
    vm
    cB
    cpw
    #
    crab
    #
    wcel
    #
    cX
    cS
    cI
    cfv
    #
    wcel
    #
    cS
    cX
    cN
    cfv
    #
    wcel
    wph
    cS
    @3
    wcel
    @5
    @7
    wb
    ntrnei.s
    @2
    @7
    vm
    cS
    @3
    @0
    cS
    wceq
    @1
    @6
    cX
    @0
    cS
    cI
    fveq2
    eleq2d
    elrab3
    syl
    wph
    @4
    @8
    cS
    wph
    cX
    cI
    cF
    cfv
    #
    cfv
    @4
    @8
    wph
    vm
    vl
    @3
    cB
    vk
    cI
    cF
    @9
    cO
    cvv
    cvv
    cX
    vi
    vj
    ntrnei.o
    wph
    cB
    cvv
    wcel
    @3
    cvv
    wcel
    wph
    cB
    vi
    vj
    vk
    vm
    cF
    cI
    cN
    cO
    vl
    ntrnei.o
    ntrnei.f
    ntrnei.r
    ntrneibex
    #
    cB
    cvv
    pwexg
    syl
    @10
    ntrnei.f
    wph
    cB
    vi
    vj
    vk
    vm
    cF
    cI
    cN
    cO
    vl
    ntrnei.o
    ntrnei.f
    ntrnei.r
    ntrneiiex
    @9
    eqid
    ntrnei.x
    fsovfvfvd
    wph
    cX
    @9
    cN
    wph
    cB
    vi
    vj
    vk
    vm
    cF
    cI
    cN
    cO
    vl
    ntrnei.o
    ntrnei.f
    ntrnei.r
    ntrneifv1
    fveq1d
    eqtr3d
    eleq2d
    bitr3d
end

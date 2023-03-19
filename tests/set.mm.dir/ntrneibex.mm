include "cpw.mm"
include "cvv.mm"
include "cv.mm"
include "cmap.mm"
include "co.mm"
include "cfv.mm"
include "wcel.mm"
include "crab.mm"
include "cmpt.mm"
include "cmpt2.mm"
include "weq.mm"
include "oveq2.mm"
include "rabeq.mm"
include "mpteq2dv.mm"
include "mpteq12dv.mm"
include "pweq.mm"
include "oveq1d.mm"
include "mpteq1.mm"
include "cbvmpt2v.mm"
include "eqtri.mm"
include "wceq.mm"
include "a1i.mm"
include "brovmptimex2.mm"

theorem ntrneibex
  let wph: wff ph
  let cB: class B
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let cF: class F
  let cI: class I
  let cN: class N
  let cO: class O
  let vl: setvar l
  let vb: setvar b
  let va: setvar a
  assume ntrnei.o: |- O = ( i e. _V , j e. _V |-> ( k e. ( ~P j ^m i ) |-> ( l e. j |-> { m e. i | l e. ( k ` m ) } ) ) )
  assume ntrnei.f: |- F = ( ~P B O B )
  assume ntrnei.r: |- ( ph -> I F N )

  disjoint i j
  disjoint i k
  disjoint j k
  disjoint i l
  disjoint j l
  disjoint i m
  disjoint j m
  disjoint O b
  disjoint a b
  disjoint a i
  disjoint a j
  disjoint a k
  disjoint b i
  disjoint b j
  disjoint b k
  disjoint a l
  disjoint b l
  disjoint a m
  disjoint b m
  assert |- ( ph -> B e. _V )

  proof
    wph
    va
    vb
    cI
    cN
    cB
    cpw
    #
    cB
    cF
    cvv
    cO
    cvv
    vk
    vb
    cv
    #
    cpw
    #
    va
    cv
    #
    cmap
    co
    #
    vl
    @1
    vl
    cv
    vm
    cv
    vk
    cv
    cfv
    wcel
    #
    vm
    @3
    crab
    #
    cmpt
    #
    cmpt
    #
    cO
    vi
    vj
    cvv
    cvv
    vk
    vj
    cv
    #
    cpw
    #
    vi
    cv
    #
    cmap
    co
    #
    vl
    @9
    @5
    vm
    @11
    crab
    #
    cmpt
    #
    cmpt
    #
    cmpt2
    va
    vb
    cvv
    cvv
    @8
    cmpt2
    ntrnei.o
    vi
    vj
    va
    vb
    cvv
    cvv
    @15
    @8
    vk
    @10
    @3
    cmap
    co
    #
    vl
    @9
    @6
    cmpt
    #
    cmpt
    vi
    va
    weq
    #
    vk
    @12
    @14
    @16
    @17
    @11
    @3
    @10
    cmap
    oveq2
    @18
    vl
    @9
    @13
    @6
    @5
    vm
    @11
    @3
    rabeq
    mpteq2dv
    mpteq12dv
    vj
    vb
    weq
    #
    vk
    @16
    @17
    @4
    @7
    @19
    @10
    @2
    @3
    cmap
    @9
    @1
    pweq
    oveq1d
    vl
    @9
    @1
    @6
    mpteq1
    mpteq12dv
    cbvmpt2v
    eqtri
    ntrnei.r
    cF
    @0
    cB
    cO
    co
    wceq
    wph
    ntrnei.f
    a1i
    brovmptimex2
end

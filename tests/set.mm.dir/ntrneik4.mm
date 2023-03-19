include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "cpw.mm"
include "wral.mm"
include "wcel.mm"
include "wb.mm"
include "wel.mm"
include "wrex.mm"
include "ntrneik4w.mm"
include "wa.mm"
include "wbr.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "ntrneiiex.mm"
include "elmapi.mm"
include "syl.mm"
include "ffvelrnda.mm"
include "adantlr.mm"
include "ntrneiel.mm"
include "simpr.mm"
include "ntrneiel2.mm"
include "bitr3d.mm"
include "bibi2d.mm"
include "ralbidva.mm"
include "bitrd.mm"

theorem ntrneik4
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let cB: class B
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let cF: class F
  let cI: class I
  let cN: class N
  let cO: class O
  let vs: setvar s
  let vl: setvar l
  assume ntrnei.o: |- O = ( i e. _V , j e. _V |-> ( k e. ( ~P j ^m i ) |-> ( l e. j |-> { m e. i | l e. ( k ` m ) } ) ) )
  assume ntrnei.f: |- F = ( ~P B O B )
  assume ntrnei.r: |- ( ph -> I F N )

  disjoint B i
  disjoint B j
  disjoint B k
  disjoint B l
  disjoint B m
  disjoint B s
  disjoint B x
  disjoint B y
  disjoint i j
  disjoint i k
  disjoint i l
  disjoint i m
  disjoint i s
  disjoint i x
  disjoint i y
  disjoint j k
  disjoint j l
  disjoint j m
  disjoint j s
  disjoint j x
  disjoint j y
  disjoint k l
  disjoint k m
  disjoint k s
  disjoint k x
  disjoint k y
  disjoint l m
  disjoint l s
  disjoint l x
  disjoint l y
  disjoint m s
  disjoint m x
  disjoint m y
  disjoint s x
  disjoint s y
  disjoint x y
  disjoint I k
  disjoint I l
  disjoint I m
  disjoint I x
  disjoint I y
  disjoint i ph
  disjoint j ph
  disjoint k ph
  disjoint l ph
  disjoint ph s
  disjoint ph x
  disjoint B u
  disjoint s u
  disjoint u x
  disjoint u y
  disjoint N u
  disjoint N y
  disjoint ph u
  disjoint ph y
  assert |- ( ph -> ( A. s e. ~P B ( I ` ( I ` s ) ) = ( I ` s ) <-> A. x e. B A. s e. ~P B ( s e. ( N ` x ) <-> E. u e. ( N ` x ) A. y e. B ( y e. u <-> s e. ( N ` y ) ) ) ) )

  proof
    wph
    vs
    cv
    #
    cI
    cfv
    #
    cI
    cfv
    #
    @1
    wceq
    vs
    cB
    cpw
    #
    wral
    @0
    vx
    cv
    #
    cN
    cfv
    #
    wcel
    #
    @1
    @5
    wcel
    #
    wb
    #
    vs
    @3
    wral
    #
    vx
    cB
    wral
    @6
    vy
    vu
    wel
    @0
    vy
    cv
    cN
    cfv
    wcel
    wb
    vy
    cB
    wral
    vu
    @5
    wrex
    #
    wb
    #
    vs
    @3
    wral
    #
    vx
    cB
    wral
    wph
    vx
    cB
    vi
    vj
    vk
    vm
    cF
    cI
    cN
    cO
    vs
    vl
    ntrnei.o
    ntrnei.f
    ntrnei.r
    ntrneik4w
    wph
    @9
    @12
    vx
    cB
    wph
    @4
    cB
    wcel
    #
    wa
    #
    @8
    @11
    vs
    @3
    @14
    @0
    @3
    wcel
    #
    wa
    #
    @7
    @10
    @6
    @16
    @4
    @2
    wcel
    @7
    @10
    @16
    cB
    @1
    vi
    vj
    vk
    vm
    cF
    cI
    cN
    cO
    @4
    vl
    ntrnei.o
    ntrnei.f
    wph
    cI
    cN
    cF
    wbr
    @13
    @15
    ntrnei.r
    ad2antrr
    #
    wph
    @13
    @15
    simplr
    #
    wph
    @15
    @1
    @3
    wcel
    @13
    wph
    @3
    @3
    @0
    cI
    wph
    cI
    @3
    @3
    cmap
    co
    wcel
    @3
    @3
    cI
    wf
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
    cI
    @3
    @3
    elmapi
    syl
    ffvelrnda
    adantlr
    ntrneiel
    @16
    vy
    vu
    cB
    @0
    vi
    vj
    vk
    vm
    cF
    cI
    cN
    cO
    @4
    vl
    ntrnei.o
    ntrnei.f
    @17
    @18
    @14
    @15
    simpr
    ntrneiel2
    bitr3d
    bibi2d
    ralbidva
    ralbidva
    bitrd
end

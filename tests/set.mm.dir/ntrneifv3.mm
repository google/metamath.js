include "cpw.mm"
include "cfv.mm"
include "cin.mm"
include "cv.mm"
include "wcel.mm"
include "crab.mm"
include "dfin5.mm"
include "wss.mm"
include "wceq.mm"
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "ntrneinex.mm"
include "elmapi.mm"
include "syl.mm"
include "ffvelrnd.mm"
include "elpwid.mm"
include "sseqin2.mm"
include "sylib.mm"
include "wa.mm"
include "wbr.mm"
include "adantr.mm"
include "simpr.mm"
include "ntrneiel.mm"
include "bicomd.mm"
include "rabbidva.mm"
include "3eqtr3a.mm"

theorem ntrneifv3
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
  let cX: class X
  let vs: setvar s
  let vl: setvar l
  assume ntrnei.o: |- O = ( i e. _V , j e. _V |-> ( k e. ( ~P j ^m i ) |-> ( l e. j |-> { m e. i | l e. ( k ` m ) } ) ) )
  assume ntrnei.f: |- F = ( ~P B O B )
  assume ntrnei.r: |- ( ph -> I F N )
  assume ntrnei.x: |- ( ph -> X e. B )

  disjoint B i
  disjoint B j
  disjoint B k
  disjoint B l
  disjoint B m
  disjoint B s
  disjoint i j
  disjoint i k
  disjoint i l
  disjoint i m
  disjoint i s
  disjoint j k
  disjoint j l
  disjoint j m
  disjoint j s
  disjoint k l
  disjoint k m
  disjoint k s
  disjoint l m
  disjoint l s
  disjoint m s
  disjoint I k
  disjoint I l
  disjoint I m
  disjoint N s
  disjoint X l
  disjoint X m
  disjoint X s
  disjoint i ph
  disjoint j ph
  disjoint k ph
  disjoint l ph
  disjoint ph s
  assert |- ( ph -> ( N ` X ) = { s e. ~P B | X e. ( I ` s ) } )

  proof
    wph
    cB
    cpw
    #
    cX
    cN
    cfv
    #
    cin
    #
    vs
    cv
    #
    @1
    wcel
    #
    vs
    @0
    crab
    @1
    cX
    @3
    cI
    cfv
    wcel
    #
    vs
    @0
    crab
    vs
    @0
    @1
    dfin5
    wph
    @1
    @0
    wss
    @2
    @1
    wceq
    wph
    @1
    @0
    wph
    cB
    @0
    cpw
    #
    cX
    cN
    wph
    cN
    @6
    cB
    cmap
    co
    wcel
    cB
    @6
    cN
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
    ntrneinex
    cN
    @6
    cB
    elmapi
    syl
    ntrnei.x
    ffvelrnd
    elpwid
    @1
    @0
    sseqin2
    sylib
    wph
    @4
    @5
    vs
    @0
    wph
    @3
    @0
    wcel
    #
    wa
    #
    @5
    @4
    @8
    cB
    @3
    vi
    vj
    vk
    vm
    cF
    cI
    cN
    cO
    cX
    vl
    ntrnei.o
    ntrnei.f
    wph
    cI
    cN
    cF
    wbr
    @7
    ntrnei.r
    adantr
    wph
    cX
    cB
    wcel
    @7
    ntrnei.x
    adantr
    wph
    @7
    simpr
    ntrneiel
    bicomd
    rabbidva
    3eqtr3a
end

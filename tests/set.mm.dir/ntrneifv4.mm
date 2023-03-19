include "cfv.mm"
include "cin.mm"
include "cv.mm"
include "wcel.mm"
include "crab.mm"
include "dfin5.mm"
include "wss.mm"
include "wceq.mm"
include "cpw.mm"
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "ntrneiiex.mm"
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
include "rabbidva.mm"
include "3eqtr3a.mm"

theorem ntrneifv4
  let wph: wff ph
  let vx: setvar x
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
  let vl: setvar l
  assume ntrnei.o: |- O = ( i e. _V , j e. _V |-> ( k e. ( ~P j ^m i ) |-> ( l e. j |-> { m e. i | l e. ( k ` m ) } ) ) )
  assume ntrnei.f: |- F = ( ~P B O B )
  assume ntrnei.r: |- ( ph -> I F N )
  assume ntrneifv.s: |- ( ph -> S e. ~P B )

  disjoint B i
  disjoint B j
  disjoint B k
  disjoint B l
  disjoint B m
  disjoint B x
  disjoint i j
  disjoint i k
  disjoint i l
  disjoint i m
  disjoint i x
  disjoint j k
  disjoint j l
  disjoint j m
  disjoint j x
  disjoint k l
  disjoint k m
  disjoint k x
  disjoint l m
  disjoint l x
  disjoint m x
  disjoint I k
  disjoint I l
  disjoint I m
  disjoint I x
  disjoint S m
  disjoint S x
  disjoint i ph
  disjoint j ph
  disjoint k ph
  disjoint l ph
  disjoint ph x
  assert |- ( ph -> ( I ` S ) = { x e. B | S e. ( N ` x ) } )

  proof
    wph
    cB
    cS
    cI
    cfv
    #
    cin
    #
    vx
    cv
    #
    @0
    wcel
    #
    vx
    cB
    crab
    @0
    cS
    @2
    cN
    cfv
    wcel
    #
    vx
    cB
    crab
    vx
    cB
    @0
    dfin5
    wph
    @0
    cB
    wss
    @1
    @0
    wceq
    wph
    @0
    cB
    wph
    cB
    cpw
    #
    @5
    cS
    cI
    wph
    cI
    @5
    @5
    cmap
    co
    wcel
    @5
    @5
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
    @5
    @5
    elmapi
    syl
    ntrneifv.s
    ffvelrnd
    elpwid
    @0
    cB
    sseqin2
    sylib
    wph
    @3
    @4
    vx
    cB
    wph
    @2
    cB
    wcel
    #
    wa
    cB
    cS
    vi
    vj
    vk
    vm
    cF
    cI
    cN
    cO
    @2
    vl
    ntrnei.o
    ntrnei.f
    wph
    cI
    cN
    cF
    wbr
    @6
    ntrnei.r
    adantr
    wph
    @6
    simpr
    wph
    cS
    @5
    wcel
    @6
    ntrneifv.s
    adantr
    ntrneiel
    rabbidva
    3eqtr3a
end

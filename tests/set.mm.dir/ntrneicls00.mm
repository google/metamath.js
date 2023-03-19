include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "wral.mm"
include "wss.mm"
include "cpw.mm"
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "ntrneiiex.mm"
include "elmapi.mm"
include "syl.mm"
include "cvv.mm"
include "ntrneibex.mm"
include "pwidg.mm"
include "ffvelrnd.mm"
include "elpwid.mm"
include "wa.mm"
include "wb.mm"
include "eqss.mm"
include "dfss3.mm"
include "anbi2i.mm"
include "bitri.mm"
include "a1i.mm"
include "mpbirand.mm"
include "wbr.mm"
include "adantr.mm"
include "simpr.mm"
include "ntrneiel.mm"
include "ralbidva.mm"
include "bitrd.mm"

theorem ntrneicls00
  let wph: wff ph
  let vx: setvar x
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
  assume ntrnei.o: |- O = ( i e. _V , j e. _V |-> ( k e. ( ~P j ^m i ) |-> ( l e. j |-> { m e. i | l e. ( k ` m ) } ) ) )
  assume ntrnei.f: |- F = ( ~P B O B )
  assume ntrnei.r: |- ( ph -> I F N )

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
  disjoint i ph
  disjoint j ph
  disjoint k ph
  disjoint l ph
  disjoint ph x
  assert |- ( ph -> ( ( I ` B ) = B <-> A. x e. B B e. ( N ` x ) ) )

  proof
    wph
    cB
    cI
    cfv
    #
    cB
    wceq
    #
    vx
    cv
    #
    @0
    wcel
    #
    vx
    cB
    wral
    #
    cB
    @2
    cN
    cfv
    wcel
    #
    vx
    cB
    wral
    wph
    @1
    @0
    cB
    wss
    #
    @4
    wph
    @0
    cB
    wph
    cB
    cpw
    #
    @7
    cB
    cI
    wph
    cI
    @7
    @7
    cmap
    co
    wcel
    @7
    @7
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
    @7
    @7
    elmapi
    syl
    wph
    cB
    cvv
    wcel
    cB
    @7
    wcel
    #
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
    cB
    cvv
    pwidg
    syl
    #
    ffvelrnd
    elpwid
    @1
    @6
    @4
    wa
    #
    wb
    wph
    @1
    @6
    cB
    @0
    wss
    #
    wa
    @10
    @0
    cB
    eqss
    @11
    @4
    @6
    vx
    cB
    @0
    dfss3
    anbi2i
    bitri
    a1i
    mpbirand
    wph
    @3
    @5
    vx
    cB
    wph
    @2
    cB
    wcel
    #
    wa
    cB
    cB
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
    @12
    ntrnei.r
    adantr
    wph
    @12
    simpr
    wph
    @8
    @12
    @9
    adantr
    ntrneiel
    ralbidva
    bitrd
end

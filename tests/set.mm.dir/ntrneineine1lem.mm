include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "wn.mm"
include "cpw.mm"
include "wrex.mm"
include "wne.mm"
include "wa.mm"
include "wbr.mm"
include "adantr.mm"
include "simpr.mm"
include "ntrneiel.mm"
include "notbid.mm"
include "rexbidva.mm"
include "wss.mm"
include "wo.mm"
include "wb.mm"
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "ntrneinex.mm"
include "elmapi.mm"
include "syl.mm"
include "ffvelrnd.mm"
include "elpwid.mm"
include "biortn.mm"
include "wex.mm"
include "df-rex.mm"
include "nss.mm"
include "bitr4i.mm"
include "wceq.mm"
include "df-ne.mm"
include "ianor.mm"
include "eqss.mm"
include "xchnxbir.mm"
include "bitri.mm"
include "3bitr4g.mm"
include "bitrd.mm"

theorem ntrneineine1lem
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
  assert |- ( ph -> ( E. s e. ~P B -. X e. ( I ` s ) <-> ( N ` X ) =/= ~P B ) )

  proof
    wph
    cX
    vs
    cv
    #
    cI
    cfv
    wcel
    #
    wn
    #
    vs
    cB
    cpw
    #
    wrex
    @0
    cX
    cN
    cfv
    #
    wcel
    #
    wn
    #
    vs
    @3
    wrex
    #
    @4
    @3
    wne
    #
    wph
    @2
    @6
    vs
    @3
    wph
    @0
    @3
    wcel
    #
    wa
    #
    @1
    @5
    @10
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
    cX
    vl
    ntrnei.o
    ntrnei.f
    wph
    cI
    cN
    cF
    wbr
    @9
    ntrnei.r
    adantr
    wph
    cX
    cB
    wcel
    @9
    ntrnei.x
    adantr
    wph
    @9
    simpr
    ntrneiel
    notbid
    rexbidva
    wph
    @3
    @4
    wss
    #
    wn
    #
    @4
    @3
    wss
    #
    wn
    @12
    wo
    #
    @7
    @8
    wph
    @13
    @12
    @14
    wb
    wph
    @4
    @3
    wph
    cB
    @3
    cpw
    #
    cX
    cN
    wph
    cN
    @15
    cB
    cmap
    co
    wcel
    cB
    @15
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
    @15
    cB
    elmapi
    syl
    ntrnei.x
    ffvelrnd
    elpwid
    @13
    @12
    biortn
    syl
    @7
    @9
    @6
    wa
    vs
    wex
    @12
    @6
    vs
    @3
    df-rex
    vs
    @3
    @4
    nss
    bitr4i
    @8
    @4
    @3
    wceq
    #
    wn
    @14
    @4
    @3
    df-ne
    @13
    @11
    wa
    @14
    @16
    @13
    @11
    ianor
    @4
    @3
    eqss
    xchnxbir
    bitri
    3bitr4g
    bitrd
end

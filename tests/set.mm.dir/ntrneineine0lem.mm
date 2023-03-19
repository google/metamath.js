include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "cpw.mm"
include "wrex.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "wbr.mm"
include "adantr.mm"
include "simpr.mm"
include "ntrneiel.mm"
include "rexbidva.mm"
include "wex.mm"
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "ntrneinex.mm"
include "elmapi.mm"
include "syl.mm"
include "ffvelrnd.mm"
include "elpwid.mm"
include "sseld.mm"
include "pm4.71rd.mm"
include "exbidv.mm"
include "bicomd.mm"
include "df-rex.mm"
include "n0.mm"
include "3bitr4g.mm"
include "bitrd.mm"

theorem ntrneineine0lem
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
  disjoint N s
  disjoint X l
  disjoint X m
  disjoint X s
  disjoint l s
  disjoint m s
  disjoint i ph
  disjoint j ph
  disjoint k ph
  disjoint l ph
  disjoint ph s
  disjoint i s
  disjoint j s
  disjoint k s
  assert |- ( ph -> ( E. s e. ~P B X e. ( I ` s ) <-> ( N ` X ) =/= (/) ) )

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
    vs
    @2
    wrex
    #
    @3
    c0
    wne
    #
    wph
    @1
    @4
    vs
    @2
    wph
    @0
    @2
    wcel
    #
    wa
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
    rexbidva
    wph
    @7
    @4
    wa
    #
    vs
    wex
    #
    @4
    vs
    wex
    #
    @5
    @6
    wph
    @10
    @9
    wph
    @4
    @8
    vs
    wph
    @4
    @7
    wph
    @3
    @2
    @0
    wph
    @3
    @2
    wph
    cB
    @2
    cpw
    #
    cX
    cN
    wph
    cN
    @11
    cB
    cmap
    co
    wcel
    cB
    @11
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
    @11
    cB
    elmapi
    syl
    ntrnei.x
    ffvelrnd
    elpwid
    sseld
    pm4.71rd
    exbidv
    bicomd
    @4
    vs
    @2
    df-rex
    vs
    @3
    n0
    3bitr4g
    bitrd
end

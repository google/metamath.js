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
include "ntrneineine0lem.mm"
include "ralbidva.mm"

theorem ntrneineine0
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
  disjoint i ph
  disjoint j ph
  disjoint k ph
  disjoint l ph
  disjoint ph s
  disjoint ph x
  disjoint i x
  disjoint j x
  disjoint k x
  disjoint l x
  disjoint s x
  disjoint m x
  assert |- ( ph -> ( A. x e. B E. s e. ~P B x e. ( I ` s ) <-> A. x e. B ( N ` x ) =/= (/) ) )

  proof
    wph
    vx
    cv
    #
    vs
    cv
    cI
    cfv
    wcel
    vs
    cB
    cpw
    wrex
    @0
    cN
    cfv
    c0
    wne
    vx
    cB
    wph
    @0
    cB
    wcel
    #
    wa
    cB
    vi
    vj
    vk
    vm
    cF
    cI
    cN
    cO
    @0
    vs
    vl
    ntrnei.o
    ntrnei.f
    wph
    cI
    cN
    cF
    wbr
    @1
    ntrnei.r
    adantr
    wph
    @1
    simpr
    ntrneineine0lem
    ralbidva
end

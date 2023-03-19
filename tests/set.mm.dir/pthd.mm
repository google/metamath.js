include "ctrls.mm"
include "cfv.mm"
include "wbr.mm"
include "c1.mm"
include "chash.mm"
include "cfzo.mm"
include "co.mm"
include "cres.mm"
include "ccnv.mm"
include "wfun.mm"
include "cc0.mm"
include "cpr.mm"
include "cima.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cpths.mm"
include "cmin.mm"
include "eqtri.mm"
include "cv.mm"
include "wne.mm"
include "wi.mm"
include "wral.mm"
include "oveq2i.mm"
include "raleqi.mm"
include "ralbii.mm"
include "sylibr.mm"
include "pthdlem1.mm"
include "pthdlem2.mm"
include "ispth.mm"
include "syl3anbrc.mm"

theorem pthd
  let wph: wff ph
  let cP: class P
  let cR: class R
  let vi: setvar i
  let vj: setvar j
  let cF: class F
  let cG: class G
  let cI: class I
  assume pthd.p: |- ( ph -> P e. Word _V )
  assume pthd.r: |- R = ( ( # ` P ) - 1 )
  assume pthd.s: |- ( ph -> A. i e. ( 0 ..^ ( # ` P ) ) A. j e. ( 1 ..^ R ) ( i =/= j -> ( P ` i ) =/= ( P ` j ) ) )
  assume pthd.f: |- ( # ` F ) = R
  assume pthd.t: |- ( ph -> F ( Trails ` G ) P )

  disjoint P i
  disjoint P j
  disjoint i j
  disjoint R i
  disjoint R j
  disjoint i ph
  disjoint j ph
  disjoint F i
  disjoint F j
  disjoint I i
  disjoint I j
  assert |- ( ph -> F ( Paths ` G ) P )

  proof
    wph
    cF
    cP
    cG
    ctrls
    cfv
    wbr
    cP
    c1
    cF
    chash
    cfv
    #
    cfzo
    co
    #
    cres
    ccnv
    wfun
    cP
    cc0
    @0
    cpr
    cima
    cP
    @1
    cima
    cin
    c0
    wceq
    cF
    cP
    cG
    cpths
    cfv
    wbr
    pthd.t
    wph
    cP
    @0
    vi
    vj
    pthd.p
    @0
    cR
    cP
    chash
    cfv
    #
    c1
    cmin
    co
    pthd.f
    pthd.r
    eqtri
    #
    wph
    vi
    cv
    #
    vj
    cv
    #
    wne
    @4
    cP
    cfv
    @5
    cP
    cfv
    wne
    wi
    #
    vj
    c1
    cR
    cfzo
    co
    #
    wral
    #
    vi
    cc0
    @2
    cfzo
    co
    #
    wral
    @6
    vj
    @1
    wral
    #
    vi
    @9
    wral
    pthd.s
    @10
    @8
    vi
    @9
    @6
    vj
    @1
    @7
    @0
    cR
    c1
    cfzo
    pthd.f
    oveq2i
    raleqi
    ralbii
    sylibr
    #
    pthdlem1
    wph
    cP
    @0
    vi
    vj
    pthd.p
    @3
    @11
    pthdlem2
    cP
    cF
    cG
    ispth
    syl3anbrc
end

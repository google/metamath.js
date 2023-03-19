include "cc0.mm"
include "wceq.mm"
include "c1.mm"
include "cabs.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "adantr.mm"
include "wa.mm"
include "wn.mm"
include "0lt1.mm"
include "0re.mm"
include "1re.mm"
include "ltnsymi.mm"
include "ax-mp.mm"
include "a1i.mm"
include "id.mm"
include "abs00bd.mm"
include "oveq2d.mm"
include "adantl.mm"
include "cc.mm"
include "wcel.mm"
include "cn.mm"
include "nncn.mm"
include "syl.mm"
include "mul01d.mm"
include "eqtrd.mm"
include "eqcomd.mm"
include "breq2d.mm"
include "mtbid.mm"
include "pm2.65da.mm"
include "neqned.mm"

theorem knoppndvlem13
  let wph: wff ph
  let cC: class C
  let cN: class N
  assume knoppndvlem13.c: |- ( ph -> C e. ( -u 1 (,) 1 ) )
  assume knoppndvlem13.n: |- ( ph -> N e. NN )
  assume knoppndvlem13.1: |- ( ph -> 1 < ( N x. ( abs ` C ) ) )


  assert |- ( ph -> C =/= 0 )

  proof
    wph
    cC
    cc0
    wph
    cC
    cc0
    wceq
    #
    c1
    cN
    cC
    cabs
    cfv
    #
    cmul
    co
    #
    clt
    wbr
    #
    wph
    @3
    @0
    knoppndvlem13.1
    adantr
    wph
    @0
    wa
    #
    c1
    cc0
    clt
    wbr
    #
    @3
    @5
    wn
    #
    @4
    cc0
    c1
    clt
    wbr
    @6
    0lt1
    cc0
    c1
    0re
    1re
    ltnsymi
    ax-mp
    a1i
    @4
    cc0
    @2
    c1
    clt
    @4
    @2
    cc0
    @4
    @2
    cN
    cc0
    cmul
    co
    #
    cc0
    @0
    @2
    @7
    wceq
    wph
    @0
    @1
    cc0
    cN
    cmul
    @0
    cC
    @0
    id
    abs00bd
    oveq2d
    adantl
    @4
    cN
    wph
    cN
    cc
    wcel
    #
    @0
    wph
    cN
    cn
    wcel
    @8
    knoppndvlem13.n
    cN
    nncn
    syl
    adantr
    mul01d
    eqtrd
    eqcomd
    breq2d
    mtbid
    pm2.65da
    neqned
end

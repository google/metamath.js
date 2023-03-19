include "cdiv.mm"
include "co.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "wn.mm"
include "0red.mm"
include "ltnled.mm"
include "mpbid.mm"
include "ge0divd.mm"
include "mtbid.mm"
include "rerpdivcld.mm"
include "mpbird.mm"

theorem divlt0gt0d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume divlt0gt0d.1: |- ( ph -> A e. RR )
  assume divlt0gt0d.2: |- ( ph -> B e. RR+ )
  assume divlt0gt0d.3: |- ( ph -> A < 0 )


  assert |- ( ph -> ( A / B ) < 0 )

  proof
    wph
    cA
    cB
    cdiv
    co
    #
    cc0
    clt
    wbr
    cc0
    @0
    cle
    wbr
    #
    wn
    wph
    cc0
    cA
    cle
    wbr
    #
    @1
    wph
    cA
    cc0
    clt
    wbr
    @2
    wn
    divlt0gt0d.3
    wph
    cA
    cc0
    divlt0gt0d.1
    wph
    0red
    #
    ltnled
    mpbid
    wph
    cA
    cB
    divlt0gt0d.1
    divlt0gt0d.2
    ge0divd
    mtbid
    wph
    @0
    cc0
    wph
    cA
    cB
    divlt0gt0d.1
    divlt0gt0d.2
    rerpdivcld
    @3
    ltnled
    mpbird
end

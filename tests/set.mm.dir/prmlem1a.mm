include "cprime.mm"
include "wcel.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cdvds.mm"
include "wn.mm"
include "wi.mm"
include "wral.mm"
include "cn.mm"
include "c1.mm"
include "clt.mm"
include "eluz2b2.mm"
include "mpbir2an.mm"
include "wceq.mm"
include "breq1.mm"
include "notbid.mm"
include "imbi2d.mm"
include "wne.mm"
include "wa.mm"
include "prmnn.mm"
include "adantr.mm"
include "csn.mm"
include "cdif.mm"
include "eldifsn.mm"
include "n2dvds1.mm"
include "c3.mm"
include "c5.mm"
include "a1i.mm"
include "3p2e5.mm"
include "prmlem0.mm"
include "1nprm.mm"
include "pm2.21i.mm"
include "1p2e3.mm"
include "mpan.mm"
include "nnuz.mm"
include "eleq2s.mm"
include "expd.mm"
include "syl5bir.mm"
include "mpcom.mm"
include "2a1i.mm"
include "pm2.61ne.mm"
include "rgen.mm"
include "isprm5.mm"

theorem prmlem1a
  let vx: setvar x
  let cN: class N
  assume prmlem1.n: |- N e. NN
  assume prmlem1.gt: |- 1 < N
  assume prmlem1.2: |- -. 2 || N
  assume prmlem1.3: |- -. 3 || N
  assume prmlem1a.x: |- ( ( -. 2 || 5 /\ x e. ( ZZ>= ` 5 ) ) -> ( ( x e. ( Prime \ { 2 } ) /\ ( x ^ 2 ) <_ N ) -> -. x || N ) )

  disjoint N x
  assert |- N e. Prime

  proof
    cN
    cprime
    wcel
    cN
    c2
    cuz
    cfv
    wcel
    #
    vx
    cv
    #
    c2
    cexp
    co
    cN
    cle
    wbr
    #
    @1
    cN
    cdvds
    wbr
    #
    wn
    #
    wi
    #
    vx
    cprime
    wral
    @0
    cN
    cn
    wcel
    c1
    cN
    clt
    wbr
    prmlem1.n
    prmlem1.gt
    cN
    eluz2b2
    mpbir2an
    @5
    vx
    cprime
    @1
    cprime
    wcel
    #
    @5
    @2
    c2
    cN
    cdvds
    wbr
    #
    wn
    #
    wi
    @1
    c2
    @1
    c2
    wceq
    #
    @4
    @8
    @2
    @9
    @3
    @7
    @1
    c2
    cN
    cdvds
    breq1
    notbid
    imbi2d
    @1
    cn
    wcel
    #
    @6
    @1
    c2
    wne
    #
    wa
    #
    @5
    @6
    @10
    @11
    @1
    prmnn
    adantr
    @12
    @1
    cprime
    c2
    csn
    cdif
    wcel
    #
    @10
    @5
    @1
    cprime
    c2
    eldifsn
    @10
    @13
    @2
    @4
    @13
    @2
    wa
    @4
    wi
    #
    @1
    c1
    cuz
    cfv
    #
    cn
    c2
    c1
    cdvds
    wbr
    wn
    @1
    @15
    wcel
    @14
    n2dvds1
    vx
    c1
    c3
    cN
    vx
    c3
    c5
    cN
    prmlem1a.x
    c3
    cN
    cdvds
    wbr
    wn
    c3
    cprime
    wcel
    prmlem1.3
    a1i
    3p2e5
    prmlem0
    c1
    cprime
    wcel
    c1
    cN
    cdvds
    wbr
    wn
    1nprm
    pm2.21i
    1p2e3
    prmlem0
    mpan
    nnuz
    eleq2s
    expd
    syl5bir
    mpcom
    @8
    @6
    @2
    prmlem1.2
    2a1i
    pm2.61ne
    rgen
    vx
    cN
    isprm5
    mpbir2an
end

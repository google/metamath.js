include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "c2.mm"
include "cle.mm"
include "wbr.mm"
include "wo.mm"
include "cc0.mm"
include "clt.mm"
include "w3o.mm"
include "cvv.mm"
include "wcel.mm"
include "fvex.mm"
include "eqeltri.mm"
include "hashv01gt1.mm"
include "ax-mp.mm"
include "3orass.mm"
include "mpbi.mm"
include "cn0.mm"
include "cpnf.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "1p1e2.mm"
include "cz.mm"
include "wb.mm"
include "1z.mm"
include "nn0z.mm"
include "zltp1le.mm"
include "sylancr.mm"
include "biimpac.mm"
include "syl5eqbrr.mm"
include "cxr.mm"
include "2re.mm"
include "rexri.mm"
include "pnfge.mm"
include "breq2.mm"
include "mpbiri.mm"
include "adantl.mm"
include "hashnn0pnf.mm"
include "mp1i.mm"
include "mpjaodan.mm"
include "orim2i.mm"
include "wn.mm"
include "c0.mm"
include "wne.mm"
include "ne0i.mm"
include "hasheq0.mm"
include "biimpi.mm"
include "necon3ai.mm"
include "3syl.mm"
include "biorf.mm"
include "syl.mm"
include "mpbird.mm"

theorem tgldimor
  let wph: wff ph
  let cA: class A
  let cP: class P
  let cE: class E
  let cF: class F
  assume tgldimor.p: |- P = ( E ` F )
  assume tgldimor.a: |- ( ph -> A e. P )


  assert |- ( ph -> ( ( # ` P ) = 1 \/ 2 <_ ( # ` P ) ) )

  proof
    wph
    cP
    chash
    cfv
    #
    c1
    wceq
    #
    c2
    @0
    cle
    wbr
    #
    wo
    #
    @0
    cc0
    wceq
    #
    @3
    wo
    #
    @4
    @1
    c1
    @0
    clt
    wbr
    #
    wo
    #
    wo
    #
    @5
    wph
    @4
    @1
    @6
    w3o
    #
    @8
    cP
    cvv
    wcel
    #
    @9
    cP
    cF
    cE
    cfv
    cvv
    tgldimor.p
    cF
    cE
    fvex
    eqeltri
    #
    cP
    cvv
    hashv01gt1
    ax-mp
    @4
    @1
    @6
    3orass
    mpbi
    @7
    @3
    @4
    @6
    @2
    @1
    @6
    @0
    cn0
    wcel
    #
    @2
    @0
    cpnf
    wceq
    #
    @6
    @12
    wa
    c2
    c1
    c1
    caddc
    co
    #
    @0
    cle
    1p1e2
    @12
    @6
    @14
    @0
    cle
    wbr
    #
    @12
    c1
    cz
    wcel
    @0
    cz
    wcel
    @6
    @15
    wb
    1z
    @0
    nn0z
    c1
    @0
    zltp1le
    sylancr
    biimpac
    syl5eqbrr
    @13
    @2
    @6
    @13
    @2
    c2
    cpnf
    cle
    wbr
    #
    c2
    cxr
    wcel
    @16
    c2
    2re
    rexri
    c2
    pnfge
    ax-mp
    @0
    cpnf
    c2
    cle
    breq2
    mpbiri
    adantl
    @10
    @12
    @13
    wo
    @6
    @11
    cP
    cvv
    hashnn0pnf
    mp1i
    mpjaodan
    orim2i
    orim2i
    mp1i
    wph
    @4
    wn
    #
    @3
    @5
    wb
    wph
    cA
    cP
    wcel
    cP
    c0
    wne
    @17
    tgldimor.a
    cP
    cA
    ne0i
    @4
    cP
    c0
    @4
    cP
    c0
    wceq
    #
    @10
    @4
    @18
    wb
    @11
    cP
    cvv
    hasheq0
    ax-mp
    biimpi
    necon3ai
    3syl
    @4
    @3
    biorf
    syl
    mpbird
end

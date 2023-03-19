include "crusgr.mm"
include "wbr.mm"
include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "cn0.mm"
include "chash.mm"
include "cfv.mm"
include "cc0.mm"
include "cv.mm"
include "wceq.mm"
include "cwwlksn.mm"
include "co.mm"
include "crab.mm"
include "cdif.mm"
include "cmin.mm"
include "cexp.mm"
include "eqid.mm"
include "clwwlknclwwlkdif.mm"
include "fveq2i.mm"
include "a1i.mm"
include "wss.mm"
include "cvtx.mm"
include "eleq1i.mm"
include "biimpi.mm"
include "adantl.mm"
include "adantr.mm"
include "wwlksnfi.mm"
include "rabfi.mm"
include "3syl.mm"
include "cwwlksnon.mm"
include "iswwlksnon.mm"
include "ancom.mm"
include "rabbii.mm"
include "eqtri.mm"
include "syl5eq.mm"
include "wi.mm"
include "simpr.mm"
include "ss2rabi.mm"
include "syl6eqss.mm"
include "hashssdif.mm"
include "syl2anc.mm"
include "simpl.mm"
include "rusgrnumwwlkg.mm"
include "syl13anc.mm"
include "oveq1d.mm"
include "3eqtrd.mm"

theorem clwwlknclwwlkdifnum
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cG: class G
  let cK: class K
  let cN: class N
  let cV: class V
  let cX: class X
  assume clwwlknclwwlkdif.a: |- A = { w e. ( N WWalksN G ) | ( ( w ` 0 ) = X /\ ( lastS ` w ) =/= X ) }
  assume clwwlknclwwlkdif.b: |- B = ( X ( N WWalksNOn G ) X )
  assume clwwlknclwwlkdifnum.v: |- V = ( Vtx ` G )

  disjoint G w
  disjoint N w
  disjoint X w
  disjoint K w
  disjoint V w
  assert |- ( ( ( G RegUSGraph K /\ V e. Fin ) /\ ( X e. V /\ N e. NN0 ) ) -> ( # ` A ) = ( ( K ^ N ) - ( # ` B ) ) )

  proof
    cG
    cK
    crusgr
    wbr
    #
    cV
    cfn
    wcel
    #
    wa
    #
    cX
    cV
    wcel
    #
    cN
    cn0
    wcel
    #
    wa
    #
    wa
    #
    cA
    chash
    cfv
    #
    cc0
    vw
    cv
    #
    cfv
    cX
    wceq
    #
    vw
    cN
    cG
    cwwlksn
    co
    #
    crab
    #
    cB
    cdif
    #
    chash
    cfv
    #
    @11
    chash
    cfv
    #
    cB
    chash
    cfv
    #
    cmin
    co
    #
    cK
    cN
    cexp
    co
    #
    @15
    cmin
    co
    @7
    @13
    wceq
    @6
    cA
    @12
    chash
    vw
    cA
    cB
    @11
    cG
    cN
    cX
    clwwlknclwwlkdif.a
    clwwlknclwwlkdif.b
    @11
    eqid
    clwwlknclwwlkdif
    fveq2i
    a1i
    @6
    @11
    cfn
    wcel
    #
    cB
    @11
    wss
    #
    @13
    @16
    wceq
    @6
    cG
    cvtx
    cfv
    #
    cfn
    wcel
    #
    @10
    cfn
    wcel
    @18
    @2
    @21
    @5
    @1
    @21
    @0
    @1
    @21
    cV
    @20
    cfn
    clwwlknclwwlkdifnum.v
    eleq1i
    biimpi
    adantl
    adantr
    cG
    cN
    wwlksnfi
    @9
    vw
    @10
    rabfi
    3syl
    @5
    @19
    @2
    @5
    cB
    cN
    @8
    cfv
    cX
    wceq
    #
    @9
    wa
    #
    vw
    @10
    crab
    #
    @11
    @5
    cB
    cX
    cX
    cN
    cG
    cwwlksnon
    co
    co
    #
    @24
    clwwlknclwwlkdif.b
    @25
    @24
    wceq
    @5
    @25
    @9
    @22
    wa
    #
    vw
    @10
    crab
    @24
    vw
    cX
    cX
    cG
    cN
    cV
    clwwlknclwwlkdifnum.v
    iswwlksnon
    @26
    @23
    vw
    @10
    @9
    @22
    ancom
    rabbii
    eqtri
    a1i
    syl5eq
    @23
    @9
    vw
    @10
    @23
    @9
    wi
    @8
    @10
    wcel
    @22
    @9
    simpr
    a1i
    ss2rabi
    syl6eqss
    adantl
    @11
    cB
    hashssdif
    syl2anc
    @6
    @14
    @17
    @15
    cmin
    @6
    @0
    @1
    @3
    @4
    @14
    @17
    wceq
    @2
    @0
    @5
    @0
    @1
    simpl
    adantr
    @2
    @1
    @5
    @0
    @1
    simpr
    adantr
    @5
    @3
    @2
    @3
    @4
    simpl
    adantl
    @5
    @4
    @2
    @3
    @4
    simpr
    adantl
    vw
    cX
    cG
    cK
    cN
    cV
    clwwlknclwwlkdifnum.v
    rusgrnumwwlkg
    syl13anc
    oveq1d
    3eqtrd
end

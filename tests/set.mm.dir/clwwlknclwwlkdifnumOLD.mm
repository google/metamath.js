include "crusgr.mm"
include "wbr.mm"
include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "cn.mm"
include "chash.mm"
include "cfv.mm"
include "cc0.mm"
include "cv.mm"
include "wceq.mm"
include "cwwlksn.mm"
include "co.mm"
include "crab.mm"
include "cdif.mm"
include "cexp.mm"
include "cmin.mm"
include "clwwlknclwwlkdifsOLD.mm"
include "fveq2i.mm"
include "wss.mm"
include "cvtx.mm"
include "eleq1i.mm"
include "biimpi.mm"
include "adantl.mm"
include "adantr.mm"
include "wwlksnfi.mm"
include "rabfi.mm"
include "3syl.mm"
include "clsw.mm"
include "wi.mm"
include "simpr.mm"
include "a1i.mm"
include "ss2rabi.mm"
include "eqsstri.mm"
include "hashssdif.mm"
include "sylancl.mm"
include "cn0.mm"
include "simpl.mm"
include "nnnn0.mm"
include "rusgrnumwwlkg.mm"
include "syl13anc.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "syl5eq.mm"

theorem clwwlknclwwlkdifnumOLD
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cG: class G
  let cK: class K
  let cN: class N
  let cV: class V
  let cX: class X
  assume clwwlknclwwlkdifsOLD.a: |- A = { w e. ( N WWalksN G ) | ( ( w ` 0 ) = X /\ ( lastS ` w ) =/= X ) }
  assume clwwlknclwwlkdifsOLD.b: |- B = { w e. ( N WWalksN G ) | ( ( lastS ` w ) = ( w ` 0 ) /\ ( w ` 0 ) = X ) }
  assume clwwlknclwwlkdifnumOLD.v: |- V = ( Vtx ` G )

  disjoint G w
  disjoint K w
  disjoint N w
  disjoint V w
  disjoint X w
  assert |- ( ( ( G RegUSGraph K /\ V e. Fin ) /\ ( X e. V /\ N e. NN ) ) -> ( # ` A ) = ( ( K ^ N ) - ( # ` B ) ) )

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
    cn
    wcel
    #
    wa
    #
    wa
    #
    cA
    chash
    cfv
    cc0
    vw
    cv
    #
    cfv
    #
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
    cK
    cN
    cexp
    co
    #
    cB
    chash
    cfv
    #
    cmin
    co
    #
    cA
    @12
    chash
    vw
    cA
    cB
    cG
    cN
    cX
    clwwlknclwwlkdifsOLD.a
    clwwlknclwwlkdifsOLD.b
    clwwlknclwwlkdifsOLD
    fveq2i
    @6
    @13
    @11
    chash
    cfv
    #
    @15
    cmin
    co
    #
    @16
    @6
    @11
    cfn
    wcel
    #
    cB
    @11
    wss
    @13
    @18
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
    @19
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
    clwwlknclwwlkdifnumOLD.v
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
    cB
    @7
    clsw
    cfv
    @8
    wceq
    #
    @9
    wa
    #
    vw
    @10
    crab
    @11
    clwwlknclwwlkdifsOLD.b
    @23
    @9
    vw
    @10
    @23
    @9
    wi
    @7
    @10
    wcel
    @22
    @9
    simpr
    a1i
    ss2rabi
    eqsstri
    @11
    cB
    hashssdif
    sylancl
    @6
    @17
    @14
    @15
    cmin
    @6
    @0
    @1
    @3
    cN
    cn0
    wcel
    #
    @17
    @14
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
    @24
    @2
    @4
    @24
    @3
    cN
    nnnn0
    adantl
    adantl
    vw
    cX
    cG
    cK
    cN
    cV
    clwwlknclwwlkdifnumOLD.v
    rusgrnumwwlkg
    syl13anc
    oveq1d
    eqtrd
    syl5eq
end

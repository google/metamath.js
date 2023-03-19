include "crusgr.mm"
include "wbr.mm"
include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "cn.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "cc0.mm"
include "cv.mm"
include "wceq.mm"
include "clsw.mm"
include "wne.mm"
include "cwwlksn.mm"
include "crab.mm"
include "cexp.mm"
include "cmin.mm"
include "cclwwlknon.mm"
include "numclwwlkovq.mm"
include "adantl.mm"
include "fveq2d.mm"
include "cwwlksnon.mm"
include "cn0.mm"
include "nnnn0.mm"
include "eqid.mm"
include "clwwlknclwwlkdifnum.mm"
include "sylanr2.mm"
include "iswwlksnon.mm"
include "wwlknlsw.mm"
include "eqcom.mm"
include "biimpi.mm"
include "eqeqan12d.mm"
include "pm5.32da.mm"
include "ancom.mm"
include "syl6bb.mm"
include "rabbiia.mm"
include "eqtri.mm"
include "fveq2i.mm"
include "a1i.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "cvv.mm"
include "wf1o.mm"
include "wex.mm"
include "ovex.mm"
include "rabex.mm"
include "clwwlkvbij.mm"
include "hasheqf1oi.mm"
include "mpsyl.mm"
include "3eqtrd.mm"

theorem numclwwlkqhash
  let vw: setvar w
  let vv: setvar v
  let cQ: class Q
  let vn: setvar n
  let cG: class G
  let cK: class K
  let cN: class N
  let cV: class V
  let cX: class X
  let vf: setvar f
  assume numclwwlk.v: |- V = ( Vtx ` G )
  assume numclwwlk.q: |- Q = ( v e. V , n e. NN |-> { w e. ( n WWalksN G ) | ( ( w ` 0 ) = v /\ ( lastS ` w ) =/= v ) } )

  disjoint G n
  disjoint G v
  disjoint G w
  disjoint n v
  disjoint n w
  disjoint v w
  disjoint N n
  disjoint N v
  disjoint N w
  disjoint V n
  disjoint V v
  disjoint X n
  disjoint X v
  disjoint X w
  disjoint K w
  disjoint V w
  disjoint G f
  disjoint f w
  disjoint N f
  disjoint V f
  disjoint X f
  assert |- ( ( ( G RegUSGraph K /\ V e. Fin ) /\ ( X e. V /\ N e. NN ) ) -> ( # ` ( X Q N ) ) = ( ( K ^ N ) - ( # ` ( X ( ClWWalksNOn ` G ) N ) ) ) )

  proof
    cG
    cK
    crusgr
    wbr
    cV
    cfn
    wcel
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
    cX
    cN
    cQ
    co
    #
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
    @6
    clsw
    cfv
    #
    cX
    wne
    wa
    vw
    cN
    cG
    cwwlksn
    co
    #
    crab
    #
    chash
    cfv
    #
    cK
    cN
    cexp
    co
    #
    @9
    @7
    wceq
    #
    @8
    wa
    #
    vw
    @10
    crab
    #
    chash
    cfv
    #
    cmin
    co
    #
    @13
    cX
    cN
    cG
    cclwwlknon
    cfv
    co
    #
    chash
    cfv
    #
    cmin
    co
    @4
    @5
    @11
    chash
    @3
    @5
    @11
    wceq
    @0
    vw
    vv
    cQ
    vn
    cG
    cN
    cV
    cX
    numclwwlk.v
    numclwwlk.q
    numclwwlkovq
    adantl
    fveq2d
    @4
    @12
    @13
    cX
    cX
    cN
    cG
    cwwlksnon
    co
    co
    #
    chash
    cfv
    #
    cmin
    co
    #
    @18
    @2
    @0
    @1
    cN
    cn0
    wcel
    @12
    @23
    wceq
    cN
    nnnn0
    vw
    @11
    @21
    cG
    cK
    cN
    cV
    cX
    @11
    eqid
    @21
    eqid
    numclwwlk.v
    clwwlknclwwlkdifnum
    sylanr2
    @4
    @22
    @17
    @13
    cmin
    @22
    @17
    wceq
    @4
    @21
    @16
    chash
    @21
    @8
    cN
    @6
    cfv
    #
    cX
    wceq
    #
    wa
    #
    vw
    @10
    crab
    @16
    vw
    cX
    cX
    cG
    cN
    cV
    numclwwlk.v
    iswwlksnon
    @26
    @15
    vw
    @10
    @6
    @10
    wcel
    #
    @26
    @8
    @14
    wa
    @15
    @27
    @8
    @25
    @14
    @27
    @8
    @24
    @9
    cX
    @7
    cG
    cN
    @6
    wwlknlsw
    @8
    cX
    @7
    wceq
    @7
    cX
    eqcom
    biimpi
    eqeqan12d
    pm5.32da
    @8
    @14
    ancom
    syl6bb
    rabbiia
    eqtri
    fveq2i
    a1i
    oveq2d
    eqtrd
    @4
    @17
    @20
    @13
    cmin
    @16
    cvv
    wcel
    @4
    @16
    @19
    vf
    cv
    wf1o
    vf
    wex
    #
    @17
    @20
    wceq
    @15
    vw
    @10
    cN
    cG
    cwwlksn
    ovex
    rabex
    @3
    @28
    @0
    vw
    vf
    cG
    cN
    cV
    cX
    numclwwlk.v
    clwwlkvbij
    adantl
    @16
    @19
    vf
    cvv
    hasheqf1oi
    mpsyl
    oveq2d
    3eqtrd
end

include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "cress.mm"
include "co.mm"
include "cin.mm"
include "wceq.mm"
include "wi.mm"
include "cbs.mm"
include "cfv.mm"
include "wss.mm"
include "w3a.mm"
include "wn.mm"
include "cnx.mm"
include "cop.mm"
include "csts.mm"
include "simplr.mm"
include "simpr1.mm"
include "simpr2.mm"
include "eqid.mm"
include "ressval2.mm"
include "syl3anc.mm"
include "inass.mm"
include "in12.mm"
include "eqtri.mm"
include "ressbas.mm"
include "syl.mm"
include "ineq2d.mm"
include "syl5req.mm"
include "opeq2d.mm"
include "oveq12d.mm"
include "fvex.mm"
include "inex2.mm"
include "setsabs.mm"
include "sylancl.mm"
include "eqtrd.mm"
include "simpll.mm"
include "ovexd.mm"
include "simpr3.mm"
include "inss1.mm"
include "sstr.mm"
include "mpan2.mm"
include "nsyl.mm"
include "inex1g.mm"
include "3eqtr4d.mm"
include "exp31.mm"
include "ovex.mm"
include "ressid2.mm"
include "mp3an2.mm"
include "3ad2antr3.mm"
include "in32.mm"
include "simpl.mm"
include "eqsstrd.mm"
include "df-ss.mm"
include "sylib.mm"
include "oveq2d.mm"
include "ressinbas.mm"
include "3syl.mm"
include "ex.mm"
include "3adant3r3.mm"
include "oveq1d.mm"
include "inss2.mm"
include "syl5ss.mm"
include "sseqin2.mm"
include "pm2.61ii.mm"
include "3expib.mm"
include "c0.mm"
include "ress0.mm"
include "reldmress.mm"
include "ovprc1.mm"
include "3eqtr4a.mm"
include "a1d.mm"
include "pm2.61i.mm"

theorem ressress
  let cA: class A
  let cB: class B
  let cW: class W
  let cX: class X
  let cY: class Y


  assert |- ( ( A e. X /\ B e. Y ) -> ( ( W |`s A ) |`s B ) = ( W |`s ( A i^i B ) ) )

  proof
    cW
    cvv
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cY
    wcel
    #
    wa
    #
    cW
    cA
    cress
    co
    #
    cB
    cress
    co
    #
    cW
    cA
    cB
    cin
    #
    cress
    co
    #
    wceq
    #
    wi
    @0
    @1
    @2
    @8
    @4
    cbs
    cfv
    #
    cB
    wss
    #
    cW
    cbs
    cfv
    #
    cA
    wss
    #
    @0
    @1
    @2
    w3a
    #
    @8
    wi
    @10
    wn
    #
    @12
    wn
    #
    @13
    @8
    @14
    @15
    wa
    #
    @13
    wa
    #
    @4
    cnx
    cbs
    cfv
    #
    cB
    @9
    cin
    #
    cop
    #
    csts
    co
    #
    cW
    @18
    @6
    @11
    cin
    #
    cop
    #
    csts
    co
    #
    @5
    @7
    @17
    @21
    cW
    @18
    cA
    @11
    cin
    #
    cop
    csts
    co
    #
    @23
    csts
    co
    #
    @24
    @17
    @4
    @26
    @20
    @23
    csts
    @17
    @15
    @0
    @1
    @4
    @26
    wceq
    @14
    @15
    @13
    simplr
    #
    @16
    @0
    @1
    @2
    simpr1
    #
    @16
    @0
    @1
    @2
    simpr2
    #
    cA
    @11
    @4
    cW
    cvv
    cX
    @4
    eqid
    #
    @11
    eqid
    #
    ressval2
    syl3anc
    @17
    @19
    @22
    @18
    @17
    @22
    cB
    @25
    cin
    #
    @19
    @22
    cA
    cB
    @11
    cin
    #
    cin
    #
    @33
    cA
    cB
    @11
    inass
    #
    cA
    cB
    @11
    in12
    eqtri
    @17
    @25
    @9
    cB
    @17
    @1
    @25
    @9
    wceq
    #
    @30
    cA
    @11
    @4
    cX
    cW
    @31
    @32
    ressbas
    #
    syl
    ineq2d
    syl5req
    opeq2d
    oveq12d
    @17
    @0
    @22
    cvv
    wcel
    @27
    @24
    wceq
    @29
    @11
    @6
    cW
    cbs
    fvex
    inex2
    @18
    @25
    @22
    cW
    cvv
    cvv
    setsabs
    sylancl
    eqtrd
    @17
    @14
    @4
    cvv
    wcel
    #
    @2
    @5
    @21
    wceq
    @14
    @15
    @13
    simpll
    @17
    cW
    cA
    cress
    ovexd
    @16
    @0
    @1
    @2
    simpr3
    cB
    @9
    @5
    @4
    cvv
    cY
    @5
    eqid
    #
    @9
    eqid
    #
    ressval2
    syl3anc
    @17
    @11
    @6
    wss
    #
    wn
    @0
    @6
    cvv
    wcel
    #
    @7
    @24
    wceq
    @17
    @12
    @42
    @28
    @42
    @6
    cA
    wss
    @12
    cA
    cB
    inss1
    @11
    @6
    cA
    sstr
    mpan2
    nsyl
    @29
    @17
    @1
    @43
    @30
    cA
    cB
    cX
    inex1g
    #
    syl
    @6
    @11
    @7
    cW
    cvv
    cvv
    @7
    eqid
    @32
    ressval2
    syl3anc
    3eqtr4d
    exp31
    @10
    @13
    @8
    @10
    @13
    wa
    #
    @5
    @4
    @7
    @10
    @0
    @2
    @5
    @4
    wceq
    #
    @1
    @10
    @39
    @2
    @46
    cW
    cA
    cress
    ovex
    cB
    @9
    @5
    @4
    cvv
    cY
    @40
    @41
    ressid2
    mp3an2
    3ad2antr3
    @45
    cW
    @25
    cress
    co
    #
    cW
    @22
    cress
    co
    #
    @4
    @7
    @45
    @25
    @22
    cW
    cress
    @45
    @22
    @25
    cB
    cin
    #
    @25
    cA
    cB
    @11
    in32
    @45
    @25
    cB
    wss
    @49
    @25
    wceq
    @45
    @25
    @9
    cB
    @45
    @1
    @37
    @10
    @0
    @1
    @2
    simpr2
    #
    @38
    syl
    @10
    @13
    simpl
    eqsstrd
    @25
    cB
    df-ss
    sylib
    syl5req
    oveq2d
    @45
    @1
    @4
    @47
    wceq
    @50
    cA
    @11
    cW
    cX
    @32
    ressinbas
    syl
    @45
    @1
    @43
    @7
    @48
    wceq
    #
    @50
    @44
    @6
    @11
    cW
    cvv
    @32
    ressinbas
    #
    3syl
    3eqtr4d
    eqtrd
    ex
    @12
    @13
    @8
    @12
    @13
    wa
    #
    @5
    cW
    cB
    cress
    co
    #
    @7
    @53
    @4
    cW
    cB
    cress
    @12
    @0
    @1
    @4
    cW
    wceq
    @2
    cA
    @11
    @4
    cW
    cvv
    cX
    @31
    @32
    ressid2
    3adant3r3
    oveq1d
    @53
    cW
    @34
    cress
    co
    #
    @48
    @54
    @7
    @53
    @34
    @22
    cW
    cress
    @53
    @22
    @35
    @34
    @36
    @53
    @34
    cA
    wss
    @35
    @34
    wceq
    @53
    @34
    @11
    cA
    cB
    @11
    inss2
    @12
    @13
    simpl
    syl5ss
    @34
    cA
    sseqin2
    sylib
    syl5req
    oveq2d
    @53
    @2
    @54
    @55
    wceq
    @12
    @0
    @1
    @2
    simpr3
    cB
    @11
    cW
    cY
    @32
    ressinbas
    syl
    @53
    @1
    @43
    @51
    @12
    @0
    @1
    @2
    simpr2
    @44
    @52
    3syl
    3eqtr4d
    eqtrd
    ex
    pm2.61ii
    3expib
    @0
    wn
    #
    @8
    @3
    @56
    c0
    cB
    cress
    co
    c0
    @5
    @7
    cB
    ress0
    @56
    @4
    c0
    cB
    cress
    cW
    cA
    cress
    reldmress
    ovprc1
    oveq1d
    cW
    @6
    cress
    reldmress
    ovprc1
    3eqtr4a
    a1d
    pm2.61i
end

include "cprime.mm"
include "wcel.mm"
include "cv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "cz.mm"
include "wrex.mm"
include "c4.mm"
include "cmo.mm"
include "c1.mm"
include "wo.mm"
include "wa.mm"
include "wn.mm"
include "wne.mm"
include "df-ne.mm"
include "cgcd.mm"
include "cmul.mm"
include "prmz.mm"
include "ad3antrrr.mm"
include "simplrr.mm"
include "bezout.mm"
include "syl2anc.mm"
include "simplll.mm"
include "simpllr.mm"
include "simplr.mm"
include "simprll.mm"
include "simprlr.mm"
include "simprr.mm"
include "2sqblem.mm"
include "expr.mm"
include "rexlimdvva.mm"
include "mpd.mm"
include "ex.mm"
include "impancom.mm"
include "syl5bir.mm"
include "orrd.mm"
include "1z.mm"
include "oveq1.mm"
include "sq1.mm"
include "syl6eq.mm"
include "oveq1d.mm"
include "eqeq2d.mm"
include "oveq2d.mm"
include "1p1e2.mm"
include "rspc2ev.mm"
include "mp3an12.mm"
include "adantl.mm"
include "2sq.mm"
include "jaodan.mm"
include "impbida.mm"

theorem 2sqb
  let vx: setvar x
  let vy: setvar y
  let cP: class P
  let va: setvar a
  let vb: setvar b

  disjoint x y
  disjoint P x
  disjoint P y
  disjoint a b
  disjoint a x
  disjoint a y
  disjoint P a
  disjoint b x
  disjoint b y
  disjoint P b
  assert |- ( P e. Prime -> ( E. x e. ZZ E. y e. ZZ P = ( ( x ^ 2 ) + ( y ^ 2 ) ) <-> ( P = 2 \/ ( P mod 4 ) = 1 ) ) )

  proof
    cP
    cprime
    wcel
    #
    cP
    vx
    cv
    #
    c2
    cexp
    co
    #
    vy
    cv
    #
    c2
    cexp
    co
    #
    caddc
    co
    #
    wceq
    #
    vy
    cz
    wrex
    vx
    cz
    wrex
    #
    cP
    c2
    wceq
    #
    cP
    c4
    cmo
    co
    c1
    wceq
    #
    wo
    @0
    @7
    wa
    #
    @8
    @9
    @8
    wn
    cP
    c2
    wne
    #
    @10
    @9
    cP
    c2
    df-ne
    @0
    @11
    @7
    @9
    @0
    @11
    wa
    #
    @6
    @9
    vx
    vy
    cz
    cz
    @12
    @1
    cz
    wcel
    #
    @3
    cz
    wcel
    #
    wa
    #
    wa
    #
    @6
    @9
    @16
    @6
    wa
    #
    cP
    @3
    cgcd
    co
    cP
    va
    cv
    #
    cmul
    co
    @3
    vb
    cv
    #
    cmul
    co
    caddc
    co
    wceq
    #
    vb
    cz
    wrex
    va
    cz
    wrex
    #
    @9
    @17
    cP
    cz
    wcel
    #
    @14
    @21
    @0
    @22
    @11
    @15
    @6
    cP
    prmz
    ad3antrrr
    @12
    @13
    @14
    @6
    simplrr
    va
    vb
    cP
    @3
    bezout
    syl2anc
    @17
    @20
    @9
    va
    vb
    cz
    cz
    @17
    @18
    cz
    wcel
    #
    @19
    cz
    wcel
    #
    wa
    #
    @20
    @9
    @17
    @25
    @20
    wa
    #
    wa
    @18
    @19
    cP
    @1
    @3
    @12
    @15
    @6
    @26
    simplll
    @12
    @15
    @6
    @26
    simpllr
    @16
    @6
    @26
    simplr
    @17
    @23
    @24
    @20
    simprll
    @17
    @23
    @24
    @20
    simprlr
    @17
    @25
    @20
    simprr
    2sqblem
    expr
    rexlimdvva
    mpd
    ex
    rexlimdvva
    impancom
    syl5bir
    orrd
    @0
    @8
    @7
    @9
    @8
    @7
    @0
    c1
    cz
    wcel
    #
    @27
    @8
    @7
    1z
    1z
    @6
    @8
    cP
    c1
    @4
    caddc
    co
    #
    wceq
    vx
    vy
    c1
    c1
    cz
    cz
    @1
    c1
    wceq
    #
    @5
    @28
    cP
    @29
    @2
    c1
    @4
    caddc
    @29
    @2
    c1
    c2
    cexp
    co
    #
    c1
    @1
    c1
    c2
    cexp
    oveq1
    sq1
    syl6eq
    oveq1d
    eqeq2d
    @3
    c1
    wceq
    #
    @28
    c2
    cP
    @31
    @28
    c1
    c1
    caddc
    co
    c2
    @31
    @4
    c1
    c1
    caddc
    @31
    @4
    @30
    c1
    @3
    c1
    c2
    cexp
    oveq1
    sq1
    syl6eq
    oveq2d
    1p1e2
    syl6eq
    eqeq2d
    rspc2ev
    mp3an12
    adantl
    vx
    vy
    cP
    2sq
    jaodan
    impbida
end

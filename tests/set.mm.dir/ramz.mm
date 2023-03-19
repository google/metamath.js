include "cn0.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "cc0.mm"
include "csn.mm"
include "cxp.mm"
include "cram.mm"
include "co.mm"
include "wceq.mm"
include "cn.mm"
include "wo.mm"
include "wa.mm"
include "wi.mm"
include "elnn0.mm"
include "cv.mm"
include "wex.mm"
include "n0.mm"
include "wf.mm"
include "cfv.mm"
include "simpll.mm"
include "simplr.mm"
include "0nn0.mm"
include "fconst6.mm"
include "a1i.mm"
include "simpr.mm"
include "fvconst2g.mm"
include "sylancr.mm"
include "ramz2.mm"
include "syl32anc.mm"
include "ex.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "expimpd.mm"
include "crn.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "cz.mm"
include "wrex.mm"
include "simpl.mm"
include "0z.mm"
include "elsni.mm"
include "0le0.mm"
include "syl6eqbr.mm"
include "rgen.mm"
include "rnxp.mm"
include "adantl.mm"
include "raleqdv.mm"
include "mpbiri.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "0ram.mm"
include "syl31anc.mm"
include "supeq1d.mm"
include "wor.mm"
include "ltso.mm"
include "0re.mm"
include "supsn.mm"
include "mp2an.mm"
include "3eqtrd.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "syl5ibr.mm"
include "jaoi.mm"
include "sylbi.mm"
include "3impib.mm"

theorem ramz
  let cR: class R
  let cM: class M
  let cV: class V
  let vb: setvar b
  let vd: setvar d
  let vz: setvar z
  let vc: setvar c
  let vf: setvar f
  let vs: setvar s
  let vx: setvar x
  let cC: class C
  let va: setvar a
  let vi: setvar i
  let vy: setvar y
  let cF: class F


  assert |- ( ( M e. NN0 /\ R e. V /\ R =/= (/) ) -> ( M Ramsey ( R X. { 0 } ) ) = 0 )

  proof
    cM
    cn0
    wcel
    #
    cR
    cV
    wcel
    #
    cR
    c0
    wne
    #
    cM
    cR
    cc0
    csn
    #
    cxp
    #
    cram
    co
    #
    cc0
    wceq
    #
    @0
    cM
    cn
    wcel
    #
    cM
    cc0
    wceq
    #
    wo
    @1
    @2
    wa
    #
    @6
    wi
    #
    cM
    elnn0
    @7
    @10
    @8
    @7
    @1
    @2
    @6
    @2
    vc
    cv
    #
    cR
    wcel
    #
    vc
    wex
    @7
    @1
    wa
    #
    @6
    vc
    cR
    n0
    @13
    @12
    @6
    vc
    @13
    @12
    @6
    @13
    @12
    wa
    #
    @7
    @1
    cR
    cn0
    @4
    wf
    #
    @12
    @11
    @4
    cfv
    cc0
    wceq
    #
    @6
    @7
    @1
    @12
    simpll
    @7
    @1
    @12
    simplr
    @15
    @14
    cR
    cc0
    cn0
    0nn0
    fconst6
    #
    a1i
    @13
    @12
    simpr
    #
    @14
    cc0
    cn0
    wcel
    @12
    @16
    0nn0
    @18
    cR
    cc0
    @11
    cn0
    fvconst2g
    sylancr
    @11
    cR
    @4
    cM
    cV
    ramz2
    syl32anc
    ex
    exlimdv
    syl5bi
    expimpd
    @9
    @6
    @8
    cc0
    @4
    cram
    co
    #
    cc0
    wceq
    @9
    @19
    @4
    crn
    #
    cr
    clt
    csup
    #
    @3
    cr
    clt
    csup
    #
    cc0
    @9
    @1
    @2
    @15
    vy
    cv
    #
    vx
    cv
    #
    cle
    wbr
    #
    vy
    @20
    wral
    #
    vx
    cz
    wrex
    #
    @19
    @21
    wceq
    @1
    @2
    simpl
    @1
    @2
    simpr
    @15
    @9
    @17
    a1i
    @9
    cc0
    cz
    wcel
    @23
    cc0
    cle
    wbr
    #
    vy
    @20
    wral
    #
    @27
    0z
    @9
    @29
    @28
    vy
    @3
    wral
    @28
    vy
    @3
    @23
    @3
    wcel
    @23
    cc0
    cc0
    cle
    @23
    cc0
    elsni
    0le0
    syl6eqbr
    rgen
    @9
    @28
    vy
    @20
    @3
    @2
    @20
    @3
    wceq
    @1
    cR
    @3
    rnxp
    adantl
    #
    raleqdv
    mpbiri
    @26
    @29
    vx
    cc0
    cz
    @24
    cc0
    wceq
    @25
    @28
    vy
    @20
    @24
    cc0
    @23
    cle
    breq2
    ralbidv
    rspcev
    sylancr
    vx
    vy
    cR
    @4
    cV
    0ram
    syl31anc
    @9
    cr
    @20
    @3
    clt
    @30
    supeq1d
    @22
    cc0
    wceq
    #
    @9
    cr
    clt
    wor
    cc0
    cr
    wcel
    @31
    ltso
    0re
    cr
    cc0
    clt
    supsn
    mp2an
    a1i
    3eqtrd
    @8
    @5
    @19
    cc0
    cM
    cc0
    @4
    cram
    oveq1
    eqeq1d
    syl5ibr
    jaoi
    sylbi
    3impib
end

include "cz.mm"
include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "cc0.mm"
include "wceq.mm"
include "c0g.mm"
include "clt.mm"
include "wbr.mm"
include "cplusg.mm"
include "cn.mm"
include "csn.mm"
include "cxp.mm"
include "c1.mm"
include "cseq.mm"
include "cneg.mm"
include "cminusg.mm"
include "cif.mm"
include "cmpt2.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "wss.mm"
include "wi.mm"
include "ssel.mm"
include "anim12d.mm"
include "syl.mm"
include "imp.mm"
include "syldan.mm"
include "grpidpropd.mm"
include "3ad2ant1.mm"
include "1zzd.mm"
include "cuz.mm"
include "vex.mm"
include "fvconst2.mm"
include "nnuz.mm"
include "eqcomi.mm"
include "eleq2s.mm"
include "adantl.mm"
include "simp3.mm"
include "sseldd.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "3ad2antl1.mm"
include "seqfeq3.mm"
include "fveq1d.mm"
include "grpinvpropd.mm"
include "fveq12d.mm"
include "ifeq12d.mm"
include "mpt2eq3dva.mm"
include "eqidd.mm"
include "mpt2eq123dv.mm"
include "3eqtr3d.mm"
include "eqid.mm"
include "mulgfval.mm"
include "3eqtr4g.mm"

theorem mulgpropd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let c.x: class .x.
  let c.xp: class .X.
  let cG: class G
  let cH: class H
  let cK: class K
  let va: setvar a
  let vb: setvar b
  assume mulgpropd.m: |- .x. = ( .g ` G )
  assume mulgpropd.n: |- .X. = ( .g ` H )
  assume mulgpropd.b1: |- ( ph -> B = ( Base ` G ) )
  assume mulgpropd.b2: |- ( ph -> B = ( Base ` H ) )
  assume mulgpropd.i: |- ( ph -> B C_ K )
  assume mulgpropd.k: |- ( ( ph /\ ( x e. K /\ y e. K ) ) -> ( x ( +g ` G ) y ) e. K )
  assume mulgpropd.e: |- ( ( ph /\ ( x e. K /\ y e. K ) ) -> ( x ( +g ` G ) y ) = ( x ( +g ` H ) y ) )

  disjoint ph x
  disjoint ph y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint G x
  disjoint G y
  disjoint H x
  disjoint H y
  disjoint K x
  disjoint K y
  disjoint a ph
  disjoint b ph
  disjoint a b
  disjoint a x
  disjoint a y
  disjoint b x
  disjoint b y
  disjoint G a
  disjoint G b
  disjoint H a
  disjoint H b
  assert |- ( ph -> .x. = .X. )

  proof
    wph
    va
    vb
    cz
    cG
    cbs
    cfv
    #
    va
    cv
    #
    cc0
    wceq
    #
    cG
    c0g
    cfv
    #
    cc0
    @1
    clt
    wbr
    #
    @1
    cG
    cplusg
    cfv
    #
    cn
    vb
    cv
    #
    csn
    cxp
    #
    c1
    cseq
    #
    cfv
    #
    @1
    cneg
    #
    @8
    cfv
    #
    cG
    cminusg
    cfv
    #
    cfv
    #
    cif
    #
    cif
    #
    cmpt2
    #
    va
    vb
    cz
    cH
    cbs
    cfv
    #
    @2
    cH
    c0g
    cfv
    #
    @4
    @1
    cH
    cplusg
    cfv
    #
    @7
    c1
    cseq
    #
    cfv
    #
    @10
    @20
    cfv
    #
    cH
    cminusg
    cfv
    #
    cfv
    #
    cif
    #
    cif
    #
    cmpt2
    #
    c.x
    c.xp
    wph
    va
    vb
    cz
    cB
    @15
    cmpt2
    va
    vb
    cz
    cB
    @26
    cmpt2
    @16
    @27
    wph
    va
    vb
    cz
    cB
    @15
    @26
    wph
    @1
    cz
    wcel
    #
    @6
    cB
    wcel
    #
    w3a
    #
    @2
    @3
    @18
    @14
    @25
    wph
    @28
    @3
    @18
    wceq
    @29
    wph
    vx
    vy
    cB
    cG
    cH
    mulgpropd.b1
    mulgpropd.b2
    wph
    vx
    cv
    #
    cB
    wcel
    #
    vy
    cv
    #
    cB
    wcel
    #
    wa
    #
    @31
    cK
    wcel
    #
    @33
    cK
    wcel
    #
    wa
    #
    @31
    @33
    @5
    co
    #
    @31
    @33
    @19
    co
    wceq
    #
    wph
    @35
    @38
    wph
    cB
    cK
    wss
    #
    @35
    @38
    wi
    mulgpropd.i
    @41
    @32
    @36
    @34
    @37
    cB
    cK
    @31
    ssel
    cB
    cK
    @33
    ssel
    anim12d
    syl
    imp
    mulgpropd.e
    syldan
    #
    grpidpropd
    3ad2ant1
    @30
    @4
    @9
    @21
    @13
    @24
    @30
    @1
    @8
    @20
    @30
    vx
    vy
    @5
    @19
    cK
    @7
    c1
    @30
    1zzd
    @30
    @31
    c1
    cuz
    cfv
    #
    wcel
    #
    wa
    @31
    @7
    cfv
    #
    @6
    cK
    @44
    @45
    @6
    wceq
    #
    @30
    @46
    @31
    cn
    @43
    cn
    @6
    @31
    vb
    vex
    fvconst2
    cn
    @43
    nnuz
    eqcomi
    eleq2s
    adantl
    @30
    @6
    cK
    wcel
    @44
    @30
    cB
    cK
    @6
    wph
    @28
    @41
    @29
    mulgpropd.i
    3ad2ant1
    wph
    @28
    @29
    simp3
    sseldd
    adantr
    eqeltrd
    wph
    @28
    @38
    @39
    cK
    wcel
    @29
    mulgpropd.k
    3ad2antl1
    wph
    @28
    @38
    @40
    @29
    mulgpropd.e
    3ad2antl1
    seqfeq3
    #
    fveq1d
    @30
    @11
    @22
    @12
    @23
    wph
    @28
    @12
    @23
    wceq
    @29
    wph
    vx
    vy
    cB
    cG
    cH
    mulgpropd.b1
    mulgpropd.b2
    @42
    grpinvpropd
    3ad2ant1
    @30
    @10
    @8
    @20
    @47
    fveq1d
    fveq12d
    ifeq12d
    ifeq12d
    mpt2eq3dva
    wph
    va
    vb
    cz
    cB
    @15
    cz
    @0
    @15
    wph
    cz
    eqidd
    #
    mulgpropd.b1
    wph
    @15
    eqidd
    mpt2eq123dv
    wph
    va
    vb
    cz
    cB
    @26
    cz
    @17
    @26
    @48
    mulgpropd.b2
    wph
    @26
    eqidd
    mpt2eq123dv
    3eqtr3d
    vb
    @0
    @5
    c.x
    va
    cG
    @12
    @3
    @0
    eqid
    @5
    eqid
    @3
    eqid
    @12
    eqid
    mulgpropd.m
    mulgfval
    vb
    @17
    @19
    c.xp
    va
    cH
    @23
    @18
    @17
    eqid
    @19
    eqid
    @18
    eqid
    @23
    eqid
    mulgpropd.n
    mulgfval
    3eqtr4g
end

include "cc0.mm"
include "cv.mm"
include "cfzo.mm"
include "co.mm"
include "wf.mm"
include "ccom.mm"
include "wbr.mm"
include "cn0.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "cdm.mm"
include "wral.mm"
include "simpr.mm"
include "adantr.mm"
include "simprl.mm"
include "wf1o.mm"
include "motf1o.mm"
include "f1of.mm"
include "syl.mm"
include "ad2antrr.mm"
include "fco.mm"
include "syl2anc.mm"
include "fdm.mm"
include "eleqtrd.mm"
include "fvco3.mm"
include "simprr.mm"
include "oveq12d.mm"
include "ffvelrnd.mm"
include "cismt.mm"
include "ad3antrrr.mm"
include "motcgr.mm"
include "eqtrd.mm"
include "ralrimivva.mm"
include "cr.mm"
include "wss.mm"
include "fzo0ssnn0.mm"
include "nn0ssre.mm"
include "sstri.mm"
include "a1i.mm"
include "iscgrgd.mm"
include "mpbird.mm"
include "cword.mm"
include "wrex.mm"
include "iswrd.mm"
include "sylib.mm"
include "r19.29a.mm"

theorem motcgrg
  let wph: wff ph
  let cP: class P
  let c.sm: class .~
  let cT: class T
  let vf: setvar f
  let vg: setvar g
  let cF: class F
  let cG: class G
  let cI: class I
  let c.mi: class .-
  let cV: class V
  let vn: setvar n
  let va: setvar a
  let vb: setvar b
  let cH: class H
  let vh: setvar h
  assume ismot.p: |- P = ( Base ` G )
  assume ismot.m: |- .- = ( dist ` G )
  assume motgrp.1: |- ( ph -> G e. V )
  assume motgrp.i: |- I = { <. ( Base ` ndx ) , ( G Ismt G ) >. , <. ( +g ` ndx ) , ( f e. ( G Ismt G ) , g e. ( G Ismt G ) |-> ( f o. g ) ) >. }
  assume motcgrg.r: |- .~ = ( cgrG ` G )
  assume motcgrg.t: |- ( ph -> T e. Word P )
  assume motcgrg.f: |- ( ph -> F e. ( G Ismt G ) )

  disjoint G f
  disjoint G g
  disjoint f g
  disjoint I f
  disjoint I g
  disjoint P f
  disjoint P g
  disjoint f ph
  disjoint g ph
  disjoint .~ n
  disjoint F a
  disjoint F b
  disjoint F n
  disjoint a b
  disjoint a n
  disjoint b n
  disjoint P a
  disjoint P b
  disjoint P n
  disjoint T a
  disjoint T b
  disjoint T n
  disjoint n ph
  disjoint F a
  disjoint F b
  disjoint a b
  disjoint G a
  disjoint G b
  disjoint P a
  disjoint P b
  disjoint a f
  disjoint a g
  disjoint b f
  disjoint b g
  disjoint H a
  disjoint H b
  disjoint a ph
  disjoint b ph
  disjoint G h
  disjoint f h
  disjoint g h
  disjoint I h
  disjoint P h
  disjoint a h
  disjoint b h
  disjoint h ph
  assert |- ( ph -> ( F o. T ) .~ T )

  proof
    wph
    cc0
    vn
    cv
    #
    cfzo
    co
    #
    cP
    cT
    wf
    #
    cF
    cT
    ccom
    #
    cT
    c.sm
    wbr
    #
    vn
    cn0
    wph
    @0
    cn0
    wcel
    #
    wa
    #
    @2
    wa
    #
    @4
    va
    cv
    #
    @3
    cfv
    #
    vb
    cv
    #
    @3
    cfv
    #
    c.mi
    co
    #
    @8
    cT
    cfv
    #
    @10
    cT
    cfv
    #
    c.mi
    co
    #
    wceq
    #
    vb
    @3
    cdm
    #
    wral
    va
    @17
    wral
    @7
    @16
    va
    vb
    @17
    @17
    @7
    @8
    @17
    wcel
    #
    @10
    @17
    wcel
    #
    wa
    #
    wa
    #
    @12
    @13
    cF
    cfv
    #
    @14
    cF
    cfv
    #
    c.mi
    co
    @15
    @21
    @9
    @22
    @11
    @23
    c.mi
    @21
    @2
    @8
    @1
    wcel
    @9
    @22
    wceq
    @7
    @2
    @20
    @6
    @2
    simpr
    #
    adantr
    #
    @21
    @8
    @17
    @1
    @7
    @18
    @19
    simprl
    @21
    @1
    cP
    @3
    wf
    #
    @17
    @1
    wceq
    @7
    @26
    @20
    @7
    cP
    cP
    cF
    wf
    #
    @2
    @26
    wph
    @27
    @5
    @2
    wph
    cP
    cP
    cF
    wf1o
    @27
    wph
    cP
    cF
    cG
    c.mi
    cV
    ismot.p
    ismot.m
    motgrp.1
    motcgrg.f
    motf1o
    cP
    cP
    cF
    f1of
    syl
    ad2antrr
    @24
    @1
    cP
    cP
    cF
    cT
    fco
    syl2anc
    #
    adantr
    @1
    cP
    @3
    fdm
    syl
    #
    eleqtrd
    #
    @1
    cP
    @8
    cF
    cT
    fvco3
    syl2anc
    @21
    @2
    @10
    @1
    wcel
    @11
    @23
    wceq
    @25
    @21
    @10
    @17
    @1
    @7
    @18
    @19
    simprr
    @29
    eleqtrd
    #
    @1
    cP
    @10
    cF
    cT
    fvco3
    syl2anc
    oveq12d
    @21
    @13
    @14
    cP
    cF
    cG
    c.mi
    cV
    ismot.p
    ismot.m
    @7
    cG
    cV
    wcel
    #
    @20
    wph
    @32
    @5
    @2
    motgrp.1
    ad2antrr
    #
    adantr
    @21
    @1
    cP
    @8
    cT
    @25
    @30
    ffvelrnd
    @21
    @1
    cP
    @10
    cT
    @25
    @31
    ffvelrnd
    wph
    cF
    cG
    cG
    cismt
    co
    wcel
    @5
    @2
    @20
    motcgrg.f
    ad3antrrr
    motcgr
    eqtrd
    ralrimivva
    @7
    @3
    cT
    @1
    cP
    c.sm
    va
    vb
    cG
    c.mi
    cV
    ismot.p
    ismot.m
    motcgrg.r
    @33
    @1
    cr
    wss
    @7
    @1
    cn0
    cr
    @0
    fzo0ssnn0
    nn0ssre
    sstri
    a1i
    @28
    @24
    iscgrgd
    mpbird
    wph
    cT
    cP
    cword
    wcel
    @2
    vn
    cn0
    wrex
    motcgrg.t
    cP
    cT
    vn
    iswrd
    sylib
    r19.29a
end

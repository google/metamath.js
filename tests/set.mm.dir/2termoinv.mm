include "chom.mm"
include "cfv.mm"
include "co.mm"
include "wcel.mm"
include "w3a.mm"
include "cinv.mm"
include "wbr.mm"
include "csect.mm"
include "cop.mm"
include "cco.mm"
include "ccid.mm"
include "wceq.mm"
include "cbs.mm"
include "eqid.mm"
include "ccat.mm"
include "3ad2ant1.mm"
include "ctermo.mm"
include "termoo.mm"
include "sylc.mm"
include "simp3.mm"
include "simp2.mm"
include "catcocl.mm"
include "csn.mm"
include "termoid.mm"
include "mpdan.mm"
include "eleq2d.mm"
include "elsni.mm"
include "syl6bi.mm"
include "mpd.mm"
include "issect2.mm"
include "mpbird.mm"
include "wa.mm"
include "wb.mm"
include "isinv.mm"
include "mpbir2and.mm"

theorem 2termoinv
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G
  let va: setvar a
  let vg: setvar g
  let vb: setvar b
  let vf: setvar f
  assume termoeu1.c: |- ( ph -> C e. Cat )
  assume termoeu1.a: |- ( ph -> A e. ( TermO ` C ) )
  assume termoeu1.b: |- ( ph -> B e. ( TermO ` C ) )


  assert |- ( ( ph /\ G e. ( B ( Hom ` C ) A ) /\ F e. ( A ( Hom ` C ) B ) ) -> F ( A ( Inv ` C ) B ) G )

  proof
    wph
    cG
    cB
    cA
    cC
    chom
    cfv
    #
    co
    wcel
    #
    cF
    cA
    cB
    @0
    co
    wcel
    #
    w3a
    #
    cF
    cG
    cA
    cB
    cC
    cinv
    cfv
    #
    co
    wbr
    #
    cF
    cG
    cA
    cB
    cC
    csect
    cfv
    #
    co
    wbr
    #
    cG
    cF
    cB
    cA
    @6
    co
    wbr
    #
    @3
    @7
    cG
    cF
    cA
    cB
    cop
    cA
    cC
    cco
    cfv
    #
    co
    co
    #
    cA
    cC
    ccid
    cfv
    #
    cfv
    #
    wceq
    #
    @3
    @10
    cA
    cA
    @0
    co
    #
    wcel
    #
    @13
    @3
    cC
    cbs
    cfv
    #
    cC
    @9
    cF
    cG
    @0
    cA
    cB
    cA
    @16
    eqid
    #
    @0
    eqid
    #
    @9
    eqid
    #
    wph
    @1
    cC
    ccat
    wcel
    #
    @2
    termoeu1.c
    3ad2ant1
    #
    wph
    @1
    cA
    @16
    wcel
    #
    @2
    wph
    @20
    cA
    cC
    ctermo
    cfv
    #
    wcel
    #
    @22
    termoeu1.c
    termoeu1.a
    cC
    cA
    termoo
    sylc
    #
    3ad2ant1
    #
    wph
    @1
    cB
    @16
    wcel
    #
    @2
    wph
    @20
    cB
    @23
    wcel
    #
    @27
    termoeu1.c
    termoeu1.b
    cC
    cB
    termoo
    sylc
    #
    3ad2ant1
    #
    @26
    wph
    @1
    @2
    simp3
    #
    wph
    @1
    @2
    simp2
    #
    catcocl
    @3
    @15
    @10
    @12
    csn
    #
    wcel
    @13
    @3
    @14
    @33
    @10
    wph
    @1
    @14
    @33
    wceq
    #
    @2
    wph
    @24
    @34
    termoeu1.a
    wph
    @16
    cC
    @0
    cA
    @17
    @18
    termoeu1.c
    termoid
    mpdan
    3ad2ant1
    eleq2d
    @10
    @12
    elsni
    syl6bi
    mpd
    @3
    @16
    cC
    @6
    @9
    @11
    cF
    cG
    @0
    cA
    cB
    @17
    @18
    @19
    @11
    eqid
    #
    @6
    eqid
    #
    @21
    @26
    @30
    @31
    @32
    issect2
    mpbird
    @3
    @8
    cF
    cG
    cB
    cA
    cop
    cB
    @9
    co
    co
    #
    cB
    @11
    cfv
    #
    wceq
    #
    @3
    @37
    cB
    cB
    @0
    co
    #
    wcel
    #
    @39
    @3
    @16
    cC
    @9
    cG
    cF
    @0
    cB
    cA
    cB
    @17
    @18
    @19
    @21
    @30
    @26
    @30
    @32
    @31
    catcocl
    @3
    @41
    @37
    @38
    csn
    #
    wcel
    @39
    @3
    @40
    @42
    @37
    wph
    @1
    @40
    @42
    wceq
    #
    @2
    wph
    @28
    @43
    termoeu1.b
    wph
    @16
    cC
    @0
    cB
    @17
    @18
    termoeu1.c
    termoid
    mpdan
    3ad2ant1
    eleq2d
    @37
    @38
    elsni
    syl6bi
    mpd
    @3
    @16
    cC
    @6
    @9
    @11
    cG
    cF
    @0
    cB
    cA
    @17
    @18
    @19
    @35
    @36
    @21
    @30
    @26
    @32
    @31
    issect2
    mpbird
    wph
    @1
    @5
    @7
    @8
    wa
    wb
    @2
    wph
    @16
    cC
    @6
    cF
    cG
    @4
    cA
    cB
    @17
    @4
    eqid
    termoeu1.c
    @25
    @29
    @36
    isinv
    3ad2ant1
    mpbir2and
end

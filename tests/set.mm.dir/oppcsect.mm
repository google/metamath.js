include "chom.mm"
include "cfv.mm"
include "co.mm"
include "wcel.mm"
include "cop.mm"
include "cco.mm"
include "ccid.mm"
include "wceq.mm"
include "w3a.mm"
include "wbr.mm"
include "wa.mm"
include "eqid.mm"
include "adantr.mm"
include "oppcco.mm"
include "ccat.mm"
include "oppcid.mm"
include "syl.mm"
include "fveq1d.mm"
include "eqeq12d.mm"
include "pm5.32da.mm"
include "df-3an.mm"
include "oppchom.mm"
include "eleq2i.mm"
include "anbi12ci.mm"
include "anbi1i.mm"
include "bitri.mm"
include "3bitr4g.mm"
include "oppcbas.mm"
include "oppccat.mm"
include "issect.mm"
include "3bitr4d.mm"

theorem oppcsect
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cS: class S
  let cT: class T
  let cF: class F
  let cG: class G
  let cO: class O
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vg: setvar g
  assume oppcsect.b: |- B = ( Base ` C )
  assume oppcsect.o: |- O = ( oppCat ` C )
  assume oppcsect.c: |- ( ph -> C e. Cat )
  assume oppcsect.x: |- ( ph -> X e. B )
  assume oppcsect.y: |- ( ph -> Y e. B )
  assume oppcsect.s: |- S = ( Sect ` C )
  assume oppcsect.t: |- T = ( Sect ` O )


  assert |- ( ph -> ( F ( X T Y ) G <-> G ( X S Y ) F ) )

  proof
    wph
    cF
    cX
    cY
    cO
    chom
    cfv
    #
    co
    #
    wcel
    #
    cG
    cY
    cX
    @0
    co
    #
    wcel
    #
    cG
    cF
    cX
    cY
    cop
    #
    cX
    cO
    cco
    cfv
    #
    co
    co
    #
    cX
    cO
    ccid
    cfv
    #
    cfv
    #
    wceq
    #
    w3a
    #
    cG
    cX
    cY
    cC
    chom
    cfv
    #
    co
    #
    wcel
    #
    cF
    cY
    cX
    @12
    co
    #
    wcel
    #
    cF
    cG
    @5
    cX
    cC
    cco
    cfv
    #
    co
    co
    #
    cX
    cC
    ccid
    cfv
    #
    cfv
    #
    wceq
    #
    w3a
    #
    cF
    cG
    cX
    cY
    cT
    co
    wbr
    cG
    cF
    cX
    cY
    cS
    co
    wbr
    wph
    @14
    @16
    wa
    #
    @10
    wa
    #
    @23
    @21
    wa
    @11
    @22
    wph
    @23
    @10
    @21
    wph
    @23
    wa
    #
    @7
    @18
    @9
    @20
    @25
    cB
    cC
    @17
    cF
    cG
    cO
    cX
    cY
    cX
    oppcsect.b
    @17
    eqid
    #
    oppcsect.o
    wph
    cX
    cB
    wcel
    @23
    oppcsect.x
    adantr
    #
    wph
    cY
    cB
    wcel
    @23
    oppcsect.y
    adantr
    @27
    oppcco
    @25
    cX
    @8
    @19
    @25
    cC
    ccat
    wcel
    #
    @8
    @19
    wceq
    wph
    @28
    @23
    oppcsect.c
    adantr
    @19
    cC
    cO
    oppcsect.o
    @19
    eqid
    #
    oppcid
    syl
    fveq1d
    eqeq12d
    pm5.32da
    @11
    @2
    @4
    wa
    #
    @10
    wa
    @24
    @2
    @4
    @10
    df-3an
    @30
    @23
    @10
    @2
    @16
    @4
    @14
    @1
    @15
    cF
    cC
    @12
    cO
    cX
    cY
    @12
    eqid
    #
    oppcsect.o
    oppchom
    eleq2i
    @3
    @13
    cG
    cC
    @12
    cO
    cY
    cX
    @31
    oppcsect.o
    oppchom
    eleq2i
    anbi12ci
    anbi1i
    bitri
    @14
    @16
    @21
    df-3an
    3bitr4g
    wph
    cB
    cO
    cT
    @6
    @8
    cF
    cG
    @0
    cX
    cY
    cB
    cC
    cO
    oppcsect.o
    oppcsect.b
    oppcbas
    @0
    eqid
    @6
    eqid
    @8
    eqid
    oppcsect.t
    wph
    @28
    cO
    ccat
    wcel
    oppcsect.c
    cC
    cO
    oppcsect.o
    oppccat
    syl
    oppcsect.x
    oppcsect.y
    issect
    wph
    cB
    cC
    cS
    @17
    @19
    cG
    cF
    @12
    cX
    cY
    oppcsect.b
    @31
    @26
    @29
    oppcsect.s
    oppcsect.c
    oppcsect.x
    oppcsect.y
    issect
    3bitr4d
end

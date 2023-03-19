include "crg.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "cmatrepV.mm"
include "co.mm"
include "cfv.mm"
include "cv.mm"
include "wceq.mm"
include "cif.mm"
include "cmpt2.mm"
include "eqid.mm"
include "marepvval.mm"
include "adantl.mm"
include "cbs.mm"
include "cfn.mm"
include "cvv.mm"
include "matrcl.mm"
include "simpld.mm"
include "3ad2ant1.mm"
include "simpl.mm"
include "wi.mm"
include "cmap.mm"
include "wf.mm"
include "elmapi.mm"
include "ffvelrn.mm"
include "ex.mm"
include "syl.mm"
include "eleq2s.mm"
include "3ad2ant2.mm"
include "imp.mm"
include "3adant3.mm"
include "simp2.mm"
include "simp3.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "matecl.mm"
include "syl3anc.mm"
include "ifcld.mm"
include "matbas2d.mm"
include "eqeltrd.mm"

theorem marepvcl
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cK: class K
  let cM: class M
  let cN: class N
  let cV: class V
  let vi: setvar i
  let vj: setvar j
  let cL: class L
  assume marepvcl.a: |- A = ( N Mat R )
  assume marepvcl.b: |- B = ( Base ` A )
  assume marepvcl.v: |- V = ( ( Base ` R ) ^m N )


  assert |- ( ( R e. Ring /\ ( M e. B /\ C e. V /\ K e. N ) ) -> ( ( M ( N matRepV R ) C ) ` K ) e. B )

  proof
    cR
    crg
    wcel
    #
    cM
    cB
    wcel
    #
    cC
    cV
    wcel
    #
    cK
    cN
    wcel
    #
    w3a
    #
    wa
    #
    cK
    cM
    cC
    cN
    cR
    cmatrepV
    co
    #
    co
    cfv
    #
    vi
    vj
    cN
    cN
    vj
    cv
    #
    cK
    wceq
    #
    vi
    cv
    #
    cC
    cfv
    #
    @10
    @8
    cM
    co
    #
    cif
    #
    cmpt2
    #
    cB
    @4
    @7
    @14
    wceq
    @0
    cA
    cB
    cC
    @6
    cR
    vi
    vj
    cK
    cM
    cN
    cV
    marepvcl.a
    marepvcl.b
    @6
    eqid
    marepvcl.v
    marepvval
    adantl
    @5
    vi
    vj
    cA
    cB
    @13
    cR
    cR
    cbs
    cfv
    #
    cN
    crg
    marepvcl.a
    @15
    eqid
    #
    marepvcl.b
    @4
    cN
    cfn
    wcel
    #
    @0
    @1
    @2
    @17
    @3
    @1
    @17
    cR
    cvv
    wcel
    cA
    cB
    cR
    cN
    cM
    marepvcl.a
    marepvcl.b
    matrcl
    simpld
    3ad2ant1
    adantl
    @0
    @4
    simpl
    @5
    @10
    cN
    wcel
    #
    @8
    cN
    wcel
    #
    w3a
    #
    @9
    @11
    @12
    @15
    @5
    @18
    @11
    @15
    wcel
    #
    @19
    @5
    @18
    @21
    @4
    @18
    @21
    wi
    #
    @0
    @2
    @1
    @22
    @3
    @22
    cC
    @15
    cN
    cmap
    co
    #
    cV
    cC
    @23
    wcel
    cN
    @15
    cC
    wf
    #
    @22
    cC
    @15
    cN
    elmapi
    @24
    @18
    @21
    cN
    @15
    @10
    cC
    ffvelrn
    ex
    syl
    marepvcl.v
    eleq2s
    3ad2ant2
    adantl
    imp
    3adant3
    @20
    @18
    @19
    cM
    cA
    cbs
    cfv
    #
    wcel
    #
    @12
    @15
    wcel
    @5
    @18
    @19
    simp2
    @5
    @18
    @19
    simp3
    @5
    @18
    @26
    @19
    @4
    @26
    @0
    @1
    @2
    @26
    @3
    @1
    @26
    cB
    @25
    cM
    marepvcl.b
    eleq2i
    biimpi
    3ad2ant1
    adantl
    3ad2ant1
    cA
    cR
    @10
    @8
    @15
    cM
    cN
    marepvcl.a
    @16
    matecl
    syl3anc
    ifcld
    matbas2d
    eqeltrd
end

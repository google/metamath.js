include "cphtpc.mm"
include "cfv.mm"
include "cec.mm"
include "wceq.mm"
include "cplusg.mm"
include "co.mm"
include "c0g.mm"
include "cpco.mm"
include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "csn.mm"
include "cxp.mm"
include "cbs.mm"
include "eqid.mm"
include "cuni.mm"
include "wcel.mm"
include "cii.mm"
include "ccn.mm"
include "w3a.mm"
include "pcorevcl.mm"
include "syl.mm"
include "simp1d.mm"
include "simp2d.mm"
include "eqtrd.mm"
include "simp3d.mm"
include "a1i.mm"
include "pi1eluni.mm"
include "mpbir3and.mm"
include "pi1addval.mm"
include "wer.mm"
include "phtpcer.mm"
include "wbr.mm"
include "pcorev.mm"
include "sneqd.mm"
include "xpeq2d.mm"
include "breqtrd.mm"
include "erthi.mm"
include "cgrp.mm"
include "pi1grplem.mm"
include "simprd.mm"
include "3eqtrd.mm"
include "wb.mm"
include "simpld.mm"
include "elpi1i.mm"
include "grpinvid2.mm"
include "syl3anc.mm"
include "mpbird.mm"

theorem pi1inv
  let wph: wff ph
  let vx: setvar x
  let cF: class F
  let cG: class G
  let cI: class I
  let cJ: class J
  let cN: class N
  let cX: class X
  let cY: class Y
  assume pi1grp.2: |- G = ( J pi1 Y )
  assume pi1inv.n: |- N = ( invg ` G )
  assume pi1inv.j: |- ( ph -> J e. ( TopOn ` X ) )
  assume pi1inv.y: |- ( ph -> Y e. X )
  assume pi1inv.f: |- ( ph -> F e. ( II Cn J ) )
  assume pi1inv.0: |- ( ph -> ( F ` 0 ) = Y )
  assume pi1inv.1: |- ( ph -> ( F ` 1 ) = Y )
  assume pi1inv.i: |- I = ( x e. ( 0 [,] 1 ) |-> ( F ` ( 1 - x ) ) )

  disjoint F x
  disjoint G x
  disjoint J x
  disjoint ph x
  disjoint Y x
  assert |- ( ph -> ( N ` [ F ] ( ~=ph ` J ) ) = [ I ] ( ~=ph ` J ) )

  proof
    wph
    cF
    cJ
    cphtpc
    cfv
    #
    cec
    #
    cN
    cfv
    cI
    @0
    cec
    #
    wceq
    #
    @2
    @1
    cG
    cplusg
    cfv
    #
    co
    #
    cG
    c0g
    cfv
    #
    wceq
    #
    wph
    @5
    cI
    cF
    cJ
    cpco
    cfv
    co
    #
    @0
    cec
    cc0
    c1
    cicc
    co
    #
    cY
    csn
    #
    cxp
    #
    @0
    cec
    #
    @6
    wph
    cG
    cbs
    cfv
    #
    @4
    cG
    cJ
    cI
    cF
    cX
    cY
    pi1grp.2
    @13
    eqid
    #
    pi1inv.j
    pi1inv.y
    @4
    eqid
    #
    wph
    cI
    @13
    cuni
    #
    wcel
    cI
    cii
    cJ
    ccn
    co
    #
    wcel
    #
    cc0
    cI
    cfv
    #
    cY
    wceq
    c1
    cI
    cfv
    #
    cY
    wceq
    wph
    @18
    @19
    c1
    cF
    cfv
    #
    wceq
    #
    @20
    cc0
    cF
    cfv
    #
    wceq
    #
    wph
    cF
    @17
    wcel
    #
    @18
    @22
    @24
    w3a
    pi1inv.f
    vx
    cF
    cI
    cJ
    pi1inv.i
    pcorevcl
    syl
    #
    simp1d
    #
    wph
    @19
    @21
    cY
    wph
    @18
    @22
    @24
    @26
    simp2d
    pi1inv.1
    eqtrd
    #
    wph
    @20
    @23
    cY
    wph
    @18
    @22
    @24
    @26
    simp3d
    pi1inv.0
    eqtrd
    #
    wph
    @13
    cI
    cG
    cJ
    cX
    cY
    pi1grp.2
    pi1inv.j
    pi1inv.y
    @13
    @13
    wceq
    wph
    @14
    a1i
    #
    pi1eluni
    mpbir3and
    wph
    cF
    @16
    wcel
    @25
    @23
    cY
    wceq
    @21
    cY
    wceq
    pi1inv.f
    pi1inv.0
    pi1inv.1
    wph
    @13
    cF
    cG
    cJ
    cX
    cY
    pi1grp.2
    pi1inv.j
    pi1inv.y
    @30
    pi1eluni
    mpbir3and
    pi1addval
    wph
    @8
    @11
    @0
    @17
    @17
    @0
    wer
    wph
    cJ
    phtpcer
    a1i
    wph
    @8
    @9
    @21
    csn
    #
    cxp
    #
    @11
    @0
    wph
    @25
    @8
    @32
    @0
    wbr
    pi1inv.f
    vx
    @32
    cF
    cI
    cJ
    pi1inv.i
    @32
    eqid
    pcorev
    syl
    wph
    @31
    @10
    @9
    wph
    @21
    cY
    pi1inv.1
    sneqd
    xpeq2d
    breqtrd
    erthi
    wph
    cG
    cgrp
    wcel
    #
    @12
    @6
    wceq
    #
    wph
    @13
    cG
    cJ
    cX
    cY
    @11
    pi1grp.2
    @14
    pi1inv.j
    pi1inv.y
    @11
    eqid
    pi1grplem
    #
    simprd
    3eqtrd
    wph
    @33
    @1
    @13
    wcel
    @2
    @13
    wcel
    @3
    @7
    wb
    wph
    @33
    @34
    @35
    simpld
    wph
    @13
    cF
    cG
    cJ
    cX
    cY
    pi1grp.2
    @14
    pi1inv.j
    pi1inv.y
    pi1inv.f
    pi1inv.0
    pi1inv.1
    elpi1i
    wph
    @13
    cI
    cG
    cJ
    cX
    cY
    pi1grp.2
    @14
    pi1inv.j
    pi1inv.y
    @27
    @28
    @29
    elpi1i
    @13
    @4
    cG
    cN
    @1
    @2
    @6
    @14
    @15
    @6
    eqid
    pi1inv.n
    grpinvid2
    syl3anc
    mpbird
end

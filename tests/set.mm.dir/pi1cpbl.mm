include "wbr.mm"
include "wa.mm"
include "co.mm"
include "cpco.mm"
include "cfv.mm"
include "cuni.mm"
include "wcel.mm"
include "cphtpc.mm"
include "ctopon.mm"
include "adantr.mm"
include "cbs.mm"
include "wceq.mm"
include "eqidd.mm"
include "pi1buni.mm"
include "w3a.mm"
include "simprl.mm"
include "cxp.mm"
include "cin.mm"
include "breqi.mm"
include "brinxp2.mm"
include "bitri.mm"
include "sylib.mm"
include "simp1d.mm"
include "simprr.mm"
include "om1addcl.mm"
include "simp2d.mm"
include "c1.mm"
include "cc0.mm"
include "cii.mm"
include "ccn.mm"
include "pi1eluni.mm"
include "mpbid.mm"
include "simp3d.mm"
include "eqtr4d.mm"
include "pcohtpy.mm"
include "syl3anbrc.mm"
include "cplusg.mm"
include "om1plusg.mm"
include "syl6eqr.mm"
include "oveqd.mm"
include "3brtr3d.mm"
include "ex.mm"

theorem pi1cpbl
  let wph: wff ph
  let cB: class B
  let cP: class P
  let c.pl: class .+
  let cQ: class Q
  let cR: class R
  let cG: class G
  let cJ: class J
  let cM: class M
  let cN: class N
  let cO: class O
  let cX: class X
  let cY: class Y
  let vj: setvar j
  let vx: setvar x
  let vy: setvar y
  let cK: class K
  assume pi1val.g: |- G = ( J pi1 Y )
  assume pi1val.1: |- ( ph -> J e. ( TopOn ` X ) )
  assume pi1val.2: |- ( ph -> Y e. X )
  assume pi1bas2.b: |- ( ph -> B = ( Base ` G ) )
  assume pi1bas3.r: |- R = ( ( ~=ph ` J ) i^i ( U. B X. U. B ) )
  assume pi1cpbl.o: |- O = ( J Om1 Y )
  assume pi1cpbl.a: |- .+ = ( +g ` O )


  assert |- ( ph -> ( ( M R N /\ P R Q ) -> ( M .+ P ) R ( N .+ Q ) ) )

  proof
    wph
    cM
    cN
    cR
    wbr
    #
    cP
    cQ
    cR
    wbr
    #
    wa
    #
    cM
    cP
    c.pl
    co
    #
    cN
    cQ
    c.pl
    co
    #
    cR
    wbr
    wph
    @2
    wa
    #
    cM
    cP
    cJ
    cpco
    cfv
    #
    co
    #
    cN
    cQ
    @6
    co
    #
    @3
    @4
    cR
    @5
    @7
    cB
    cuni
    #
    wcel
    #
    @8
    @9
    wcel
    #
    @7
    @8
    cJ
    cphtpc
    cfv
    #
    wbr
    #
    @7
    @8
    cR
    wbr
    #
    @5
    @9
    cM
    cJ
    cP
    cO
    cX
    cY
    pi1cpbl.o
    wph
    cJ
    cX
    ctopon
    cfv
    wcel
    @2
    pi1val.1
    adantr
    #
    wph
    cY
    cX
    wcel
    @2
    pi1val.2
    adantr
    #
    @5
    cB
    cG
    cJ
    cO
    cbs
    cfv
    #
    cO
    cX
    cY
    pi1val.g
    @15
    @16
    pi1cpbl.o
    wph
    cB
    cG
    cbs
    cfv
    wceq
    @2
    pi1bas2.b
    adantr
    #
    @5
    @17
    eqidd
    pi1buni
    #
    @5
    cM
    @9
    wcel
    #
    cN
    @9
    wcel
    #
    cM
    cN
    @12
    wbr
    #
    @5
    @0
    @20
    @21
    @22
    w3a
    #
    wph
    @0
    @1
    simprl
    @0
    cM
    cN
    @12
    @9
    @9
    cxp
    cin
    #
    wbr
    @23
    cM
    cN
    cR
    @24
    pi1bas3.r
    breqi
    cM
    cN
    @9
    @9
    @12
    brinxp2
    bitri
    sylib
    #
    simp1d
    #
    @5
    cP
    @9
    wcel
    #
    cQ
    @9
    wcel
    #
    cP
    cQ
    @12
    wbr
    #
    @5
    @1
    @27
    @28
    @29
    w3a
    #
    wph
    @0
    @1
    simprr
    @1
    cP
    cQ
    @24
    wbr
    @30
    cP
    cQ
    cR
    @24
    pi1bas3.r
    breqi
    cP
    cQ
    @9
    @9
    @12
    brinxp2
    bitri
    sylib
    #
    simp1d
    #
    om1addcl
    @5
    @9
    cN
    cJ
    cQ
    cO
    cX
    cY
    pi1cpbl.o
    @15
    @16
    @19
    @5
    @20
    @21
    @22
    @25
    simp2d
    @5
    @27
    @28
    @29
    @31
    simp2d
    om1addcl
    @5
    cM
    cP
    cN
    cJ
    cQ
    @5
    c1
    cM
    cfv
    #
    cY
    cc0
    cP
    cfv
    #
    @5
    cM
    cii
    cJ
    ccn
    co
    #
    wcel
    #
    cc0
    cM
    cfv
    cY
    wceq
    #
    @33
    cY
    wceq
    #
    @5
    @20
    @36
    @37
    @38
    w3a
    @26
    @5
    cB
    cM
    cG
    cJ
    cX
    cY
    pi1val.g
    @15
    @16
    @18
    pi1eluni
    mpbid
    simp3d
    @5
    cP
    @35
    wcel
    #
    @34
    cY
    wceq
    #
    c1
    cP
    cfv
    cY
    wceq
    #
    @5
    @27
    @39
    @40
    @41
    w3a
    @32
    @5
    cB
    cP
    cG
    cJ
    cX
    cY
    pi1val.g
    @15
    @16
    @18
    pi1eluni
    mpbid
    simp2d
    eqtr4d
    @5
    @20
    @21
    @22
    @25
    simp3d
    @5
    @27
    @28
    @29
    @31
    simp3d
    pcohtpy
    @14
    @7
    @8
    @24
    wbr
    @10
    @11
    @13
    w3a
    @7
    @8
    cR
    @24
    pi1bas3.r
    breqi
    @7
    @8
    @9
    @9
    @12
    brinxp2
    bitri
    syl3anbrc
    @5
    @6
    c.pl
    cM
    cP
    @5
    @6
    cO
    cplusg
    cfv
    c.pl
    @5
    cJ
    cO
    cX
    cY
    pi1cpbl.o
    @15
    @16
    om1plusg
    pi1cpbl.a
    syl6eqr
    #
    oveqd
    @5
    @6
    c.pl
    cN
    cQ
    @42
    oveqd
    3brtr3d
    ex
end

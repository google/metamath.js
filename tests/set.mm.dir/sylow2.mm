include "cv.mm"
include "co.mm"
include "cmpt.mm"
include "crn.mm"
include "wss.mm"
include "wceq.mm"
include "wcel.mm"
include "wa.mm"
include "cfn.mm"
include "cen.mm"
include "wbr.mm"
include "adantr.mm"
include "csubg.mm"
include "cfv.mm"
include "cslw.mm"
include "slwsubg.mm"
include "syl.mm"
include "simprl.mm"
include "eqid.mm"
include "conjsubg.mm"
include "syl2anc.mm"
include "subgss.mm"
include "ssfi.mm"
include "simprr.mm"
include "chash.mm"
include "cpc.mm"
include "cexp.mm"
include "slwhash.mm"
include "eqtr4d.mm"
include "wb.mm"
include "hashen.mm"
include "mpbid.mm"
include "conjsubgen.mm"
include "entr.mm"
include "fisseneq.mm"
include "syl3anc.mm"
include "cress.mm"
include "cpgp.mm"
include "slwpgp.mm"
include "sylow2b.mm"
include "reximddv.mm"

theorem sylow2
  let wph: wff ph
  let vx: setvar x
  let cP: class P
  let c.pl: class .+
  let vg: setvar g
  let cG: class G
  let cH: class H
  let cK: class K
  let c.mi: class .-
  let cX: class X
  assume sylow2.x: |- X = ( Base ` G )
  assume sylow2.f: |- ( ph -> X e. Fin )
  assume sylow2.h: |- ( ph -> H e. ( P pSyl G ) )
  assume sylow2.k: |- ( ph -> K e. ( P pSyl G ) )
  assume sylow2.a: |- .+ = ( +g ` G )
  assume sylow2.d: |- .- = ( -g ` G )

  disjoint .- x
  disjoint g x
  disjoint .+ g
  disjoint .+ x
  disjoint G g
  disjoint G x
  disjoint H g
  disjoint H x
  disjoint K g
  disjoint K x
  disjoint g ph
  disjoint X g
  disjoint X x
  assert |- ( ph -> E. g e. X H = ran ( x e. K |-> ( ( g .+ x ) .- g ) ) )

  proof
    wph
    cH
    vx
    cK
    vg
    cv
    #
    vx
    cv
    c.pl
    co
    @0
    c.mi
    co
    cmpt
    #
    crn
    #
    wss
    #
    cH
    @2
    wceq
    #
    vg
    cX
    wph
    @0
    cX
    wcel
    #
    @3
    wa
    #
    wa
    #
    @2
    cfn
    wcel
    #
    @3
    cH
    @2
    cen
    wbr
    #
    @4
    @7
    cX
    cfn
    wcel
    #
    @2
    cX
    wss
    #
    @8
    wph
    @10
    @6
    sylow2.f
    adantr
    @7
    @2
    cG
    csubg
    cfv
    #
    wcel
    #
    @11
    @7
    cK
    @12
    wcel
    #
    @5
    @13
    wph
    @14
    @6
    wph
    cK
    cP
    cG
    cslw
    co
    #
    wcel
    @14
    sylow2.k
    cP
    cG
    cK
    slwsubg
    syl
    #
    adantr
    #
    wph
    @5
    @3
    simprl
    #
    vx
    @0
    c.pl
    cK
    @1
    cG
    c.mi
    cX
    sylow2.x
    sylow2.a
    sylow2.d
    @1
    eqid
    #
    conjsubg
    syl2anc
    cX
    @2
    cG
    sylow2.x
    subgss
    syl
    cX
    @2
    ssfi
    syl2anc
    wph
    @5
    @3
    simprr
    @7
    cH
    cK
    cen
    wbr
    #
    cK
    @2
    cen
    wbr
    #
    @9
    wph
    @20
    @6
    wph
    cH
    chash
    cfv
    #
    cK
    chash
    cfv
    #
    wceq
    #
    @20
    wph
    @22
    cP
    cP
    cX
    chash
    cfv
    cpc
    co
    cexp
    co
    @23
    wph
    cP
    cG
    cH
    cX
    sylow2.x
    sylow2.f
    sylow2.h
    slwhash
    wph
    cP
    cG
    cK
    cX
    sylow2.x
    sylow2.f
    sylow2.k
    slwhash
    #
    eqtr4d
    wph
    cH
    cfn
    wcel
    #
    cK
    cfn
    wcel
    #
    @24
    @20
    wb
    wph
    @10
    cH
    cX
    wss
    #
    @26
    sylow2.f
    wph
    cH
    @12
    wcel
    #
    @28
    wph
    cH
    @15
    wcel
    #
    @29
    sylow2.h
    cP
    cG
    cH
    slwsubg
    syl
    #
    cX
    cH
    cG
    sylow2.x
    subgss
    syl
    cX
    cH
    ssfi
    syl2anc
    wph
    @10
    cK
    cX
    wss
    #
    @27
    sylow2.f
    wph
    @14
    @32
    @16
    cX
    cK
    cG
    sylow2.x
    subgss
    syl
    cX
    cK
    ssfi
    syl2anc
    cH
    cK
    hashen
    syl2anc
    mpbid
    adantr
    @7
    @14
    @5
    @21
    @17
    @18
    vx
    @0
    c.pl
    cK
    @1
    cG
    c.mi
    cX
    sylow2.x
    sylow2.a
    sylow2.d
    @19
    conjsubgen
    syl2anc
    cH
    cK
    @2
    entr
    syl2anc
    cH
    @2
    fisseneq
    syl3anc
    wph
    vx
    cP
    c.pl
    vg
    cG
    cH
    cK
    c.mi
    cX
    sylow2.x
    sylow2.f
    @31
    @16
    sylow2.a
    wph
    @30
    cP
    cG
    cH
    cress
    co
    #
    cpgp
    wbr
    sylow2.h
    cP
    @33
    cG
    cH
    @33
    eqid
    slwpgp
    syl
    @25
    sylow2.d
    sylow2b
    reximddv
end

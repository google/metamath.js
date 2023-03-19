include "cglb.mm"
include "cfv.mm"
include "ccnv.mm"
include "csup.mm"
include "cinf.mm"
include "cv.mm"
include "cple.mm"
include "wbr.mm"
include "wral.mm"
include "wi.mm"
include "wa.mm"
include "crio.mm"
include "wn.mm"
include "wrex.mm"
include "eqid.mm"
include "tosglblem.mm"
include "riotabidva.mm"
include "ctos.mm"
include "biid.mm"
include "glbval.mm"
include "wcel.mm"
include "wor.mm"
include "wceq.mm"
include "cid.mm"
include "cres.mm"
include "wss.mm"
include "tosso.mm"
include "ibi.mm"
include "simpld.mm"
include "cnvso.mm"
include "sylib.mm"
include "id.mm"
include "supval2.mm"
include "3syl.mm"
include "3eqtr4d.mm"
include "df-inf.mm"
include "eqcomi.mm"
include "a1i.mm"
include "eqtrd.mm"

theorem tosglb
  let wph: wff ph
  let cA: class A
  let cB: class B
  let c.lt: class .<
  let cK: class K
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  assume tosglb.b: |- B = ( Base ` K )
  assume tosglb.l: |- .< = ( lt ` K )
  assume tosglb.1: |- ( ph -> K e. Toset )
  assume tosglb.2: |- ( ph -> A C_ B )


  assert |- ( ph -> ( ( glb ` K ) ` A ) = inf ( A , B , .< ) )

  proof
    wph
    cA
    cK
    cglb
    cfv
    #
    cfv
    #
    cA
    cB
    c.lt
    ccnv
    #
    csup
    #
    cA
    cB
    c.lt
    cinf
    #
    wph
    va
    cv
    #
    vb
    cv
    #
    cK
    cple
    cfv
    #
    wbr
    vb
    cA
    wral
    vc
    cv
    #
    @6
    @7
    wbr
    vb
    cA
    wral
    @8
    @5
    @7
    wbr
    wi
    vc
    cB
    wral
    wa
    #
    va
    cB
    crio
    @5
    @6
    @2
    wbr
    wn
    vb
    cA
    wral
    @6
    @5
    @2
    wbr
    @6
    vd
    cv
    @2
    wbr
    vd
    cA
    wrex
    wi
    vb
    cB
    wral
    wa
    #
    va
    cB
    crio
    #
    @1
    @3
    wph
    @9
    @10
    va
    cB
    wph
    cA
    cB
    c.lt
    cK
    @7
    va
    vb
    vc
    vd
    tosglb.b
    tosglb.l
    tosglb.1
    tosglb.2
    @7
    eqid
    #
    tosglblem
    riotabidva
    wph
    @9
    va
    vb
    vc
    cB
    cA
    @0
    cK
    @7
    ctos
    tosglb.b
    @12
    @0
    eqid
    @9
    biid
    tosglb.1
    tosglb.2
    glbval
    wph
    cK
    ctos
    wcel
    #
    cB
    @2
    wor
    #
    @3
    @11
    wceq
    tosglb.1
    @13
    cB
    c.lt
    wor
    #
    @14
    @13
    @15
    cid
    cB
    cres
    @7
    wss
    #
    @13
    @15
    @16
    wa
    cB
    c.lt
    cK
    @7
    ctos
    tosglb.b
    @12
    tosglb.l
    tosso
    ibi
    simpld
    cB
    c.lt
    cnvso
    sylib
    @14
    va
    vb
    vd
    cB
    cA
    @2
    @14
    id
    supval2
    3syl
    3eqtr4d
    @3
    @4
    wceq
    wph
    @4
    @3
    cA
    cB
    c.lt
    df-inf
    eqcomi
    a1i
    eqtrd
end

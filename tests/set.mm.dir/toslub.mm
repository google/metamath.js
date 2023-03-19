include "cv.mm"
include "cple.mm"
include "cfv.mm"
include "wbr.mm"
include "wral.mm"
include "wi.mm"
include "wa.mm"
include "crio.mm"
include "wn.mm"
include "wrex.mm"
include "club.mm"
include "csup.mm"
include "eqid.mm"
include "toslublem.mm"
include "riotabidva.mm"
include "ctos.mm"
include "biid.mm"
include "lubval.mm"
include "wcel.mm"
include "wor.mm"
include "wceq.mm"
include "cid.mm"
include "cres.mm"
include "wss.mm"
include "tosso.mm"
include "ibi.mm"
include "simpld.mm"
include "id.mm"
include "supval2.mm"
include "3syl.mm"
include "3eqtr4d.mm"

theorem toslub
  let wph: wff ph
  let cA: class A
  let cB: class B
  let c.lt: class .<
  let cK: class K
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  assume toslub.b: |- B = ( Base ` K )
  assume toslub.l: |- .< = ( lt ` K )
  assume toslub.1: |- ( ph -> K e. Toset )
  assume toslub.2: |- ( ph -> A C_ B )


  assert |- ( ph -> ( ( lub ` K ) ` A ) = sup ( A , B , .< ) )

  proof
    wph
    vb
    cv
    #
    va
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
    @0
    vc
    cv
    #
    @2
    wbr
    vb
    cA
    wral
    @1
    @3
    @2
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
    @1
    @0
    c.lt
    wbr
    wn
    vb
    cA
    wral
    @0
    @1
    c.lt
    wbr
    @0
    vd
    cv
    c.lt
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
    cA
    cK
    club
    cfv
    #
    cfv
    cA
    cB
    c.lt
    csup
    #
    wph
    @4
    @5
    va
    cB
    wph
    cA
    cB
    c.lt
    cK
    @2
    va
    vb
    vc
    vd
    toslub.b
    toslub.l
    toslub.1
    toslub.2
    @2
    eqid
    #
    toslublem
    riotabidva
    wph
    @4
    va
    vb
    vc
    cB
    cA
    @7
    cK
    @2
    ctos
    toslub.b
    @9
    @7
    eqid
    @4
    biid
    toslub.1
    toslub.2
    lubval
    wph
    cK
    ctos
    wcel
    #
    cB
    c.lt
    wor
    #
    @8
    @6
    wceq
    toslub.1
    @10
    @11
    cid
    cB
    cres
    @2
    wss
    #
    @10
    @11
    @12
    wa
    cB
    c.lt
    cK
    @2
    ctos
    toslub.b
    @9
    toslub.l
    tosso
    ibi
    simpld
    @11
    va
    vb
    vd
    cB
    cA
    c.lt
    @11
    id
    supval2
    3syl
    3eqtr4d
end

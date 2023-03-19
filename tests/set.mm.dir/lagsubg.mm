include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "cfn.mm"
include "wa.mm"
include "chash.mm"
include "cqg.mm"
include "co.mm"
include "cqs.mm"
include "cmul.mm"
include "cdvds.mm"
include "cz.mm"
include "wbr.mm"
include "cn0.mm"
include "cpw.mm"
include "wss.mm"
include "simpr.mm"
include "pwfi.mm"
include "sylib.mm"
include "wer.mm"
include "eqid.mm"
include "eqger.mm"
include "adantr.mm"
include "qsss.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "hashcl.mm"
include "syl.mm"
include "nn0zd.mm"
include "id.mm"
include "subgss.mm"
include "syl2anr.mm"
include "dvdsmul2.mm"
include "simpl.mm"
include "lagsubg2.mm"
include "breqtrrd.mm"

theorem lagsubg
  let cG: class G
  let cX: class X
  let cY: class Y
  let wph: wff ph
  let vx: setvar x
  let c.sm: class .~
  assume lagsubg.1: |- X = ( Base ` G )


  assert |- ( ( Y e. ( SubGrp ` G ) /\ X e. Fin ) -> ( # ` Y ) || ( # ` X ) )

  proof
    cY
    cG
    csubg
    cfv
    wcel
    #
    cX
    cfn
    wcel
    #
    wa
    #
    cY
    chash
    cfv
    #
    cX
    cG
    cY
    cqg
    co
    #
    cqs
    #
    chash
    cfv
    #
    @3
    cmul
    co
    #
    cX
    chash
    cfv
    cdvds
    @2
    @6
    cz
    wcel
    @3
    cz
    wcel
    @3
    @7
    cdvds
    wbr
    @2
    @6
    @2
    @5
    cfn
    wcel
    #
    @6
    cn0
    wcel
    @2
    cX
    cpw
    #
    cfn
    wcel
    #
    @5
    @9
    wss
    @8
    @2
    @1
    @10
    @0
    @1
    simpr
    #
    cX
    pwfi
    sylib
    @2
    cX
    @4
    @0
    cX
    @4
    wer
    @1
    @4
    cG
    cX
    cY
    lagsubg.1
    @4
    eqid
    #
    eqger
    adantr
    qsss
    @9
    @5
    ssfi
    syl2anc
    @5
    hashcl
    syl
    nn0zd
    @2
    @3
    @2
    cY
    cfn
    wcel
    #
    @3
    cn0
    wcel
    @1
    @1
    cY
    cX
    wss
    @13
    @0
    @1
    id
    cX
    cY
    cG
    lagsubg.1
    subgss
    cX
    cY
    ssfi
    syl2anr
    cY
    hashcl
    syl
    nn0zd
    @6
    @3
    dvdsmul2
    syl2anc
    @2
    @4
    cG
    cX
    cY
    lagsubg.1
    @12
    @0
    @1
    simpl
    @11
    lagsubg2
    breqtrrd
end

include "wcel.mm"
include "cword.mm"
include "w3a.mm"
include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "cgsu.mm"
include "cplusg.mm"
include "cfv.mm"
include "ccom.mm"
include "cmnd.mm"
include "wceq.mm"
include "cgrp.mm"
include "symggrp.mm"
include "grpmnd.mm"
include "syl.mm"
include "eqid.mm"
include "gsumccatsn.mm"
include "syl3an1.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "gsumwcl.mm"
include "syl2anc.mm"
include "simp3.mm"
include "symgov.mm"
include "eqtrd.mm"

theorem gsumccatsymgsn
  let cA: class A
  let cB: class B
  let cG: class G
  let cV: class V
  let cW: class W
  let cZ: class Z
  assume gsumccatsymgsn.g: |- G = ( SymGrp ` A )
  assume gsumccatsymgsn.b: |- B = ( Base ` G )


  assert |- ( ( A e. V /\ W e. Word B /\ Z e. B ) -> ( G gsum ( W ++ <" Z "> ) ) = ( ( G gsum W ) o. Z ) )

  proof
    cA
    cV
    wcel
    #
    cW
    cB
    cword
    wcel
    #
    cZ
    cB
    wcel
    #
    w3a
    #
    cG
    cW
    cZ
    cs1
    cconcat
    co
    cgsu
    co
    #
    cG
    cW
    cgsu
    co
    #
    cZ
    cG
    cplusg
    cfv
    #
    co
    #
    @5
    cZ
    ccom
    #
    @0
    cG
    cmnd
    wcel
    #
    @1
    @2
    @4
    @7
    wceq
    @0
    cG
    cgrp
    wcel
    @9
    cA
    cG
    cV
    gsumccatsymgsn.g
    symggrp
    cG
    grpmnd
    syl
    #
    cB
    @6
    cG
    cW
    cZ
    gsumccatsymgsn.b
    @6
    eqid
    #
    gsumccatsn
    syl3an1
    @3
    @5
    cB
    wcel
    #
    @2
    @7
    @8
    wceq
    @3
    @9
    @1
    @12
    @0
    @1
    @9
    @2
    @10
    3ad2ant1
    @0
    @1
    @2
    simp2
    cB
    cG
    cW
    gsumccatsymgsn.b
    gsumwcl
    syl2anc
    @0
    @1
    @2
    simp3
    cA
    cB
    @6
    cG
    @5
    cZ
    gsumccatsymgsn.g
    gsumccatsymgsn.b
    @11
    symgov
    syl2anc
    eqtrd
end

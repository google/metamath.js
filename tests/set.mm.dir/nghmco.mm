include "cnghm.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cngp.mm"
include "ccom.mm"
include "cghm.mm"
include "cnmo.mm"
include "cfv.mm"
include "cmul.mm"
include "cr.mm"
include "cle.mm"
include "wbr.mm"
include "nghmrcl1.mm"
include "adantl.mm"
include "nghmrcl2.mm"
include "adantr.mm"
include "nghmghm.mm"
include "ghmco.mm"
include "syl2an.mm"
include "eqid.mm"
include "nghmcl.mm"
include "remulcl.mm"
include "nmoco.mm"
include "bddnghm.mm"
include "syl32anc.mm"

theorem nghmco
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let cG: class G


  assert |- ( ( F e. ( T NGHom U ) /\ G e. ( S NGHom T ) ) -> ( F o. G ) e. ( S NGHom U ) )

  proof
    cF
    cT
    cU
    cnghm
    co
    wcel
    #
    cG
    cS
    cT
    cnghm
    co
    wcel
    #
    wa
    cS
    cngp
    wcel
    #
    cU
    cngp
    wcel
    #
    cF
    cG
    ccom
    #
    cS
    cU
    cghm
    co
    wcel
    #
    cF
    cT
    cU
    cnmo
    co
    #
    cfv
    #
    cG
    cS
    cT
    cnmo
    co
    #
    cfv
    #
    cmul
    co
    #
    cr
    wcel
    #
    @4
    cS
    cU
    cnmo
    co
    #
    cfv
    @10
    cle
    wbr
    @4
    cS
    cU
    cnghm
    co
    wcel
    @1
    @2
    @0
    cS
    cT
    cG
    nghmrcl1
    adantl
    @0
    @3
    @1
    cT
    cU
    cF
    nghmrcl2
    adantr
    @0
    cF
    cT
    cU
    cghm
    co
    wcel
    cG
    cS
    cT
    cghm
    co
    wcel
    @5
    @1
    cT
    cU
    cF
    nghmghm
    cS
    cT
    cG
    nghmghm
    cS
    cT
    cU
    cF
    cG
    ghmco
    syl2an
    @0
    @7
    cr
    wcel
    @9
    cr
    wcel
    @11
    @1
    cT
    cU
    cF
    @6
    @6
    eqid
    #
    nghmcl
    cS
    cT
    cG
    @8
    @8
    eqid
    #
    nghmcl
    @7
    @9
    remulcl
    syl2an
    cS
    cT
    cU
    cF
    cG
    @6
    @8
    @12
    @12
    eqid
    #
    @13
    @14
    nmoco
    @10
    cS
    cU
    @4
    @12
    @15
    bddnghm
    syl32anc
end

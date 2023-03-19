include "crrext.mm"
include "wcel.mm"
include "cq.mm"
include "wa.mm"
include "crrh.mm"
include "cfv.mm"
include "cqqh.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "ctopn.mm"
include "ccnext.mm"
include "co.mm"
include "wceq.mm"
include "eqid.mm"
include "rrhval.mm"
include "fveq1d.mm"
include "adantr.mm"
include "cuni.mm"
include "cr.mm"
include "uniretop.mm"
include "ctop.mm"
include "retop.mm"
include "a1i.mm"
include "cha.mm"
include "rrexthaus.mm"
include "wss.mm"
include "qssre.mm"
include "crest.mm"
include "ccn.mm"
include "crefld.mm"
include "cnrg.mm"
include "cdr.mm"
include "cin.mm"
include "czlm.mm"
include "cnlm.mm"
include "cchr.mm"
include "cc0.mm"
include "rrextnrg.mm"
include "rrextdrg.mm"
include "elind.mm"
include "rrextnlm.mm"
include "rrextchr.mm"
include "ccnfld.mm"
include "cress.mm"
include "qqtopn.mm"
include "qqhcn.mm"
include "syl3anc.mm"
include "retopn.mm"
include "eqcomi.mm"
include "oveq1i.mm"
include "syl6eleq.mm"
include "simpr.mm"
include "cnextfres.mm"
include "eqtrd.mm"

theorem rrhqima
  let cQ: class Q
  let cR: class R


  assert |- ( ( R e. RRExt /\ Q e. QQ ) -> ( ( RRHom ` R ) ` Q ) = ( ( QQHom ` R ) ` Q ) )

  proof
    cR
    crrext
    wcel
    #
    cQ
    cq
    wcel
    #
    wa
    #
    cQ
    cR
    crrh
    cfv
    #
    cfv
    #
    cQ
    cR
    cqqh
    cfv
    #
    cioo
    crn
    ctg
    cfv
    #
    cR
    ctopn
    cfv
    #
    ccnext
    co
    cfv
    #
    cfv
    #
    cQ
    @5
    cfv
    @0
    @4
    @9
    wceq
    @1
    @0
    cQ
    @3
    @8
    cR
    @6
    @7
    crrext
    @6
    eqid
    @7
    eqid
    #
    rrhval
    fveq1d
    adantr
    @2
    cq
    @7
    cuni
    #
    cr
    @5
    @6
    @7
    cQ
    uniretop
    @11
    eqid
    @6
    ctop
    wcel
    @2
    retop
    a1i
    @0
    @7
    cha
    wcel
    @1
    cR
    @7
    @10
    rrexthaus
    adantr
    cq
    cr
    wss
    @2
    qssre
    a1i
    @0
    @5
    @6
    cq
    crest
    co
    #
    @7
    ccn
    co
    #
    wcel
    @1
    @0
    @5
    crefld
    ctopn
    cfv
    #
    cq
    crest
    co
    #
    @7
    ccn
    co
    #
    @13
    @0
    cR
    cnrg
    cdr
    cin
    wcel
    cR
    czlm
    cfv
    #
    cnlm
    wcel
    cR
    cchr
    cfv
    cc0
    wceq
    @5
    @16
    wcel
    @0
    cnrg
    cdr
    cR
    cR
    rrextnrg
    cR
    rrextdrg
    elind
    cR
    @17
    @17
    eqid
    #
    rrextnlm
    cR
    rrextchr
    ccnfld
    cq
    cress
    co
    #
    cR
    @15
    @7
    @17
    @19
    eqid
    qqtopn
    @18
    @10
    qqhcn
    syl3anc
    @15
    @12
    @7
    ccn
    @14
    @6
    cq
    crest
    @6
    @14
    retopn
    eqcomi
    oveq1i
    oveq1i
    syl6eleq
    adantr
    @0
    @1
    simpr
    cnextfres
    eqtrd
end

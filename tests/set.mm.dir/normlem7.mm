include "ccj.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "cmul.mm"
include "caddc.mm"
include "cneg.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "c2.mm"
include "csqrt.mm"
include "cr.mm"
include "wcel.mm"
include "eqid.mm"
include "normlem2.mm"
include "cjcli.mm"
include "hicli.mm"
include "mulcli.mm"
include "addcli.mm"
include "negrebi.mm"
include "mpbi.mm"
include "leabsi.mm"
include "absnegi.mm"
include "breqtrri.mm"
include "normlem6.mm"
include "negcli.mm"
include "abscli.mm"
include "2re.mm"
include "chil.mm"
include "cc0.mm"
include "hiidge0.mm"
include "hiidrcl.mm"
include "ax-mp.mm"
include "sqrtcli.mm"
include "mp2b.mm"
include "remulcli.mm"
include "letri.mm"
include "mp2an.mm"

theorem normlem7
  let cS: class S
  let cF: class F
  let cG: class G
  assume normlem1.1: |- S e. CC
  assume normlem1.2: |- F e. ~H
  assume normlem1.3: |- G e. ~H
  assume normlem7.4: |- ( abs ` S ) = 1


  assert |- ( ( ( * ` S ) x. ( F .ih G ) ) + ( S x. ( G .ih F ) ) ) <_ ( 2 x. ( ( sqrt ` ( G .ih G ) ) x. ( sqrt ` ( F .ih F ) ) ) )

  proof
    cS
    ccj
    cfv
    #
    cF
    cG
    csp
    co
    #
    cmul
    co
    #
    cS
    cG
    cF
    csp
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    @5
    cneg
    #
    cabs
    cfv
    #
    cle
    wbr
    @7
    c2
    cG
    cG
    csp
    co
    #
    csqrt
    cfv
    #
    cF
    cF
    csp
    co
    #
    csqrt
    cfv
    #
    cmul
    co
    #
    cmul
    co
    #
    cle
    wbr
    @5
    @13
    cle
    wbr
    @5
    @5
    cabs
    cfv
    @7
    cle
    @5
    @6
    cr
    wcel
    @5
    cr
    wcel
    @6
    cS
    cF
    cG
    normlem1.1
    normlem1.2
    normlem1.3
    @6
    eqid
    #
    normlem2
    @5
    @2
    @4
    @0
    @1
    cS
    normlem1.1
    cjcli
    cF
    cG
    normlem1.2
    normlem1.3
    hicli
    mulcli
    cS
    @3
    normlem1.1
    cG
    cF
    normlem1.3
    normlem1.2
    hicli
    mulcli
    addcli
    #
    negrebi
    mpbi
    #
    leabsi
    @5
    @15
    absnegi
    breqtrri
    @8
    @6
    @10
    cS
    cF
    cG
    normlem1.1
    normlem1.2
    normlem1.3
    @14
    @8
    eqid
    @10
    eqid
    normlem7.4
    normlem6
    @5
    @7
    @13
    @16
    @6
    @5
    @15
    negcli
    abscli
    c2
    @12
    2re
    @9
    @11
    cG
    chil
    wcel
    #
    cc0
    @8
    cle
    wbr
    @9
    cr
    wcel
    normlem1.3
    cG
    hiidge0
    @8
    @17
    @8
    cr
    wcel
    normlem1.3
    cG
    hiidrcl
    ax-mp
    sqrtcli
    mp2b
    cF
    chil
    wcel
    #
    cc0
    @10
    cle
    wbr
    @11
    cr
    wcel
    normlem1.2
    cF
    hiidge0
    @10
    @18
    @10
    cr
    wcel
    normlem1.2
    cF
    hiidrcl
    ax-mp
    sqrtcli
    mp2b
    remulcli
    remulcli
    letri
    mp2an
end

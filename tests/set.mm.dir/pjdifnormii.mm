include "cc0.mm"
include "cpjh.mm"
include "cfv.mm"
include "cno.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cmin.mm"
include "cle.mm"
include "wbr.mm"
include "cmv.mm"
include "csp.mm"
include "pjhclii.mm"
include "normcli.mm"
include "resqcli.mm"
include "subge0i.mm"
include "chil.mm"
include "wcel.mm"
include "wceq.mm"
include "his2sub.mm"
include "mp3an.mm"
include "pjinormii.mm"
include "oveq12i.mm"
include "eqtri.mm"
include "breq2i.mm"
include "wb.mm"
include "normge0.mm"
include "ax-mp.mm"
include "le2sqi.mm"
include "mp2an.mm"
include "3bitr4i.mm"

theorem pjdifnormii
  let cA: class A
  let cG: class G
  let cH: class H
  assume pjidm.1: |- H e. CH
  assume pjidm.2: |- A e. ~H
  assume pjsslem.1: |- G e. CH


  assert |- ( 0 <_ ( ( ( ( projh ` G ) ` A ) -h ( ( projh ` H ) ` A ) ) .ih A ) <-> ( normh ` ( ( projh ` H ) ` A ) ) <_ ( normh ` ( ( projh ` G ) ` A ) ) )

  proof
    cc0
    cA
    cG
    cpjh
    cfv
    cfv
    #
    cno
    cfv
    #
    c2
    cexp
    co
    #
    cA
    cH
    cpjh
    cfv
    cfv
    #
    cno
    cfv
    #
    c2
    cexp
    co
    #
    cmin
    co
    #
    cle
    wbr
    @5
    @2
    cle
    wbr
    #
    cc0
    @0
    @3
    cmv
    co
    cA
    csp
    co
    #
    cle
    wbr
    @4
    @1
    cle
    wbr
    #
    @2
    @5
    @1
    @0
    cA
    cG
    pjsslem.1
    pjidm.2
    pjhclii
    #
    normcli
    #
    resqcli
    @4
    @3
    cA
    cH
    pjidm.1
    pjidm.2
    pjhclii
    #
    normcli
    #
    resqcli
    subge0i
    @8
    @6
    cc0
    cle
    @8
    @0
    cA
    csp
    co
    #
    @3
    cA
    csp
    co
    #
    cmin
    co
    #
    @6
    @0
    chil
    wcel
    #
    @3
    chil
    wcel
    #
    cA
    chil
    wcel
    @8
    @16
    wceq
    @10
    @12
    pjidm.2
    @0
    @3
    cA
    his2sub
    mp3an
    @14
    @2
    @15
    @5
    cmin
    cA
    cG
    pjsslem.1
    pjidm.2
    pjinormii
    cA
    cH
    pjidm.1
    pjidm.2
    pjinormii
    oveq12i
    eqtri
    breq2i
    cc0
    @4
    cle
    wbr
    #
    cc0
    @1
    cle
    wbr
    #
    @9
    @7
    wb
    @18
    @19
    @12
    @3
    normge0
    ax-mp
    @17
    @20
    @10
    @0
    normge0
    ax-mp
    @4
    @1
    @13
    @11
    le2sqi
    mp2an
    3bitr4i
end

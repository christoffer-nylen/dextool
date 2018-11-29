/**
Copyright: Copyright (c) 2018, Joakim Brännström. All rights reserved.
License: MPL-2
Author: Joakim Brännström (joakim.brannstrom@gmx.com)

This Source Code Form is subject to the terms of the Mozilla Public License,
v.2.0. If a copy of the MPL was not distributed with this file, You can obtain
one at http://mozilla.org/MPL/2.0/.
*/
module dextool.plugin.mutate.backend.report.html.tmpl;

import dextool.plugin.mutate.backend.report.html.nodes;

@safe:

immutable htmlBegin = `<!DOCTYPE html>
<html>
<head>
<meta http-equiv="Content-Type" content="text/html;charset=UTF-8">
<title>%s</title>
</head>
`;

immutable htmlBegin2 = `
<body onload="javascript:init();">
<div id="mousehover"></div>
<style>
body {font-family: monospace; font-size: 14px;}
.mutant {display:none; background-color: yellow;}
.status_alive {background-color: lightpink;}
.status_killed {background-color: lightgreen;}
.status_killedByCompiler {background-color: mediumseagreen;}
.status_timeout {background-color: limegreen;}
.status_unknown {background-color: mistyrose;}
.hover_alive {color: lightpink;}
.hover_killed {color: lightgreen;}
.hover_killedByCompiler {color: mediumseagreen;}
.hover_timeout {color: limegreen;}
.hover_unknown {color: mistyrose;}
.literal {color: darkred;}
.keyword {color: blue;}
.comment {color: grey;}
#mousehover {
    background: grey;
    border-radius: 8px;
    -moz-border-radius: 8px;
    padding: 5px;
    display: none;
    position: absolute;
    background: #2e3639;
    color: #fff;
}
span.xx_label {
    font-weight: bold;
}
#info_wrapper {
    position: absolute;
    width: 99%;
}
#info {
    position: absolute;
    top: 0;
    width: 400px;
    background: grey;
    border-radius: 10px;
    -moz-border-radius: 10px;
    padding: 5px;
    border: 1px solid;
    opacity:0.9;

    background: #2e3639;
}
#info.fixed {
    position: fixed;
}
#info span {
    font-size: 80%;
    color: #fff;
    font-family: sans-serif;
}

#info select {
    width: 250px;
}
</style>
<div id="info_wrapper">
<div id="info" class="fixed">
<table>
  <tr>
    <td><a href="../index.html" style="color: white">Back</a></td>
  </tr>
  <tr>
    <td><span class="xx_label">Status: </span></td>
    <td><span id="current_mutant_status"></span></td>
  </tr>
  <tr>
    <td><span class="xx_label">Mutant: </span></td>
    <td>
      <select id="current_mutant">
        <option value="-1">Original</option>
      </select>
    </td>
    <td><input id="show_mutant" type="checkbox" checked=true onclick='click_show_mutant(this)'/><span class="xx_label">Show</span></td>
  </tr>
</table>
</div>
</div>
`;

immutable htmlEnd = `<script>%s</script>
</body>
</html>
`;

void addStateTableCss(HtmlNode s) {
    s.putAttr("type", "text/css");
    s.put(
            `.stat_tbl {border-collapse:collapse; border-spacing: 0;border-style: solid;border-width:1px;}`);
    s.put(`.stat_tbl td{border-style: none;}`);
    s.put(`.overlap_tbl  {border-collapse:collapse;border-spacing:0;}`);
    s.put(`.overlap_tbl td{font-family:Arial, sans-serif;font-size:14px;padding:10px 5px;border-style:solid;border-width:1px;overflow:hidden;word-break:normal;border-color:black;}`);
    s.put(`.overlap_tbl th{font-family:Arial, sans-serif;font-size:14px;font-weight:normal;padding:10px 5px;border-style:solid;border-width:1px;overflow:hidden;word-break:normal;border-color:black;}`);
    s.put(`.overlap_tbl .tg-g59y{font-weight:bold;background-color:#ffce93;border-color:#000000;text-align:left;vertical-align:top}`);
    s.put(`.overlap_tbl .tg-0lax{text-align:left;vertical-align:top}`);
    s.put(
            `.overlap_tbl .tg-0lax_dark{background-color: lightgrey;text-align:left;vertical-align:top}`);
}